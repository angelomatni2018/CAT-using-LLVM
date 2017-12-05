#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/IR/LegacyPassManager.h"

#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/SparseBitVector.h"

#include "llvm/IR/Constants.h"

#include "llvm/Analysis/AliasAnalysis.h"

#include <vector>
#include <map>
#include <set>

using namespace std;
using namespace llvm;

namespace {
  struct InstrInfo {
    Function* F;
    vector<Instruction*> instructions;
    map<Instruction*, int> instrIndices;
    map<Instruction*, set<Instruction*>> iPred; 
  };

  struct DFAInfo {
    map<Instruction*, SparseBitVector<>> gen, kill;
    map<Instruction*, SparseBitVector<>> in, out;
    vector<CallInst*> get_instrs;

    AAResults* aa;
    map<Instruction*, set<Instruction*>> aliases;
  };

  struct CAT : public FunctionPass {
    static char ID; 
    Function* create_fn;
    Function* get_fn;
    Function* add_fn;
    Function* sub_fn;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      create_fn = M.getFunction("CAT_create_signed_value");
      get_fn = M.getFunction("CAT_get_signed_value");
      add_fn = M.getFunction("CAT_binary_add");
      sub_fn = M.getFunction("CAT_binary_sub");

      return false;
    }

    // This function is invoked once per module compiled
    virtual bool runOnFunction (Function &F) {
      DFAInfo dfaInfo;
      InstrInfo instrInfo;
      instrInfo.F = &F;
      dfaInfo.aa = &(getAnalysis<AAResultsWrapperPass>().getAAResults());

      collectInstrInfo(instrInfo);

      //testInfoPrintout(instrInfo, dfaInfo);
      testAllAliasPairs(instrInfo, dfaInfo);
      return false;

      computeGenKill(instrInfo, dfaInfo);

      computeInOut(instrInfo, dfaInfo);

      //printDFA(instrInfo, dfaInfo);

      return doConstantPropogation(instrInfo, dfaInfo);
    }

    void testAllAliasPairs(InstrInfo &iInfo, DFAInfo &dfa) {
      bool isPointer, isMem;
      for (auto I : iInfo.instructions) {
        //isPointer = (I->getType()->isPointerTy());

        I->print(errs());
        errs() << "\n";

        if (auto* mem = dyn_cast<StoreInst>(I)) {
          errs() << "IS STORE INST\n";
          isMem = true;          
        } else if (auto* mem = dyn_cast<LoadInst>(I)) {
          errs() << "IS LOAD INST\n";
          isMem = true;
        } else {
          isMem = false;
        }

      
        /*if (!isMem) {
          errs() << "\n";
          continue;
        }*/

        for (auto J : iInfo.instructions) {
          //isPointer = (J->getType()->isPointerTy());
          bool isMem2;
          if (auto* mem2 = dyn_cast<StoreInst>(J)) {
            errs() << "IS STORE INST\n";
            isMem2 = true;          
          } else if (auto* mem2 = dyn_cast<LoadInst>(J)) {
            errs() << "IS LOAD INST\n";
            isMem2 = true;
          } else {
            isMem2 = false;
          }
          
          /*if (!isMem2) {
            continue;
          }*/
            
          switch(dfa.aa->alias(MemoryLocation::get(I), MemoryLocation::get(J))) {
            case NoAlias:
              errs() << "----- No alias     ";
              break;
            case MayAlias:
              errs() << "----- May alias    ";
              break;
            case PartialAlias:
              errs() << "----- Partial alias";
              break;
            case MustAlias:
              errs() << "----- Must alias   ";
              break;
            default:
              abort();
          }
          errs() << "\t";
          J->print(errs());
          errs() << "\n";
        }
        errs() << "\n";
      }
    }

    void testInfoPrintout(InstrInfo &iInfo, DFAInfo &dfa) {
      set<Instruction*> creates;
      for (auto I : iInfo.instructions) {
        if (auto* call = dyn_cast<CallInst>(I)) {
          if (create_fn == call->getCalledFunction()) {
            creates.insert(I);
            errs() << "\n";
          }
        } 
      }

      for (auto I : iInfo.instructions) {
        bool isPointer = (I->getType()->isPointerTy());

        I->print(errs());
        errs() << "\t";
        errs() << isPointer << "\n";
      
        if (!isPointer) {
          errs() << "\n";
          continue;
        }

        for (int op = 0; op < I->getNumOperands(); ++op) {
          Value* opI = I->getOperand(op);
          errs() << "-----";
          opI->print(errs());
          errs() << "\n";
     
          //Value* opV = I.getOperand(op);
          //for (auto iter = dfa.aliases.begin(); iter != dfa.aliases.end(); ++iter) {
     
          for (auto create : creates) {
            errs() << "----- For the instruction:\n-----";
            create->print(errs());
            errs() << "\n";
            switch(dfa.aa->alias(opI, create)) {
              case NoAlias:
                errs() << "----- No alias\n";
                break;
              case MayAlias:
                errs() << "----- May alias\n";
                break;
              case PartialAlias:
                errs() << "----- Partial alias\n";
                break;
              case MustAlias:
                errs() << "----- Must alias\n";
                break;
              default:
                abort();
            }
          }
        }
      }

      errs() << "\n";
    }

    void collectInstrInfo(InstrInfo &iInfo) {
      unsigned counter = 0;
      
      for (auto &B : *(iInfo.F)) {
        TerminatorInst *terminatorInst = B.getTerminator();
        unsigned numSucc = terminatorInst->getNumSuccessors();
        for (auto i = 0; i < numSucc; ++i){
          BasicBlock *succ = terminatorInst->getSuccessor(i);
          Instruction *succI = &(succ->front());
          if (iInfo.iPred.find(succI) == iInfo.iPred.end())
            iInfo.iPred[succI] = set<Instruction*>();
          iInfo.iPred[succI].insert(terminatorInst);
        }

        for (auto &I : B) {
          iInfo.instructions.push_back(&I);
          iInfo.instrIndices[&I] = counter;
          ++counter;
        }
      }
    }

    // My hacky fix for ignoring Arguments when killing
    void markKill(InstrInfo &iInfo, DFAInfo &dfa, Instruction* I, Instruction* def) {
      if (iInfo.instrIndices.find(def) != iInfo.instrIndices.end())
        dfa.kill[I].set(iInfo.instrIndices[def]);
    }

    void setKillFromUses(InstrInfo &iInfo, DFAInfo &dfa, Instruction* I, Instruction* def) {
        for (auto& U : def->uses()) {
          Instruction* user = (Instruction*)(U.getUser());
          if (auto* userCall = dyn_cast<CallInst>(user)) {
            Function* CAT_fn = userCall->getCalledFunction();
            if ((CAT_fn == add_fn || CAT_fn == sub_fn) && U.getOperandNo() == 0 && user != I) {
              markKill(iInfo, dfa, I, user);
            }
          } else if (isa<PHINode>(user)) {
            markKill(iInfo, dfa, I, user);
          }
        }
    }

    void setAliasesFor(DFAInfo &dfa, Instruction* I) {
      dfa.aliases[I] = set<Instruction*>();
      for (auto iter = dfa.aliases.begin(); iter != dfa.aliases.end(); ++iter) {
        if (I == iter->first)
          continue;
        switch(dfa.aa->alias(iter->first, I)) {
          case NoAlias:
            I->print(errs());
            errs() << "\ncan NOT alias:\n";
            iter->first->print(errs());
            errs() << "\n\n";

            break;
          case MayAlias:
          case PartialAlias:
          case MustAlias:
            I->print(errs());
            errs() << "\ncan alias:\n";
            iter->first->print(errs());
            errs() << "\n\n";

            dfa.aliases[I].insert(iter->first);
            if (dfa.aliases.find(iter->first) != dfa.aliases.end())
              dfa.aliases[iter->first].insert(I);
            break;
          default:
            abort();
        }
      }
    }

    void computeGenKill(InstrInfo &iInfo, DFAInfo &dfa) {
      unsigned counter = 0;
      // GEN, KILL, and instructions
      for (auto &B : *(iInfo.F)) {
        for (auto &I : B) {
          // Adding pointer type to list of alias-concerned instructions
          if (I.getType()->isPointerTy()) {
            setAliasesFor(dfa, &I);
            dfa.gen[&I].set(counter);
          }

          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();
            if (create_fn == callee) {
              //dfa.gen[&I].set(counter);
              setKillFromUses(iInfo, dfa, &I, call);
            } else if (add_fn == callee || sub_fn == callee) {
              //dfa.gen[&I].set(counter);
              Instruction *original_def = (Instruction*)(call->getArgOperand(0));
              markKill(iInfo, dfa, &I, original_def);

              setKillFromUses(iInfo, dfa, &I, (Instruction*)(call->getArgOperand(0)));
            } else if (get_fn == callee) {
              dfa.get_instrs.push_back(call);
            } else {
              // Kill operands (escaped variables) and their aliases
              I.print(errs());
              errs() << "\nIs killing the following:\n";
              for (int op = 0; op < I.getNumOperands(); ++op) {
                Instruction* opI = (Instruction*)I.getOperand(op);
                dfa.kill[&I].set(iInfo.instrIndices[opI]);
                for (auto aliasI : dfa.aliases[opI]) {
                  errs() << "Killing: \n";
                  aliasI->print(errs());
                  errs() << "\n";
                  dfa.kill[&I].set(iInfo.instrIndices[aliasI]);
                }
              }
            }
          } else if (isa<PHINode>(&I)) {
            dfa.gen[&I].set(counter);

            setKillFromUses(iInfo, dfa, &I, &I);
          }
          ++counter;
        }
      }
    }

    void computeInOut(InstrInfo &iInfo, DFAInfo &dfa) {
      // loop until convergence
      bool modified = true;
      while (modified) {
        modified = false;

        // Loop forwards through instructions
        for (auto bbIter = iInfo.F->getBasicBlockList().begin(); bbIter != iInfo.F->getBasicBlockList().end(); ++bbIter) {
          Instruction *pred = NULL;
          for (auto iIter = bbIter->begin(); iIter != bbIter->end(); ++iIter) {
            Instruction &I = *iIter;

            // IN = union of predecessor OUT
            if (iInfo.iPred.count(&I)) { // Front with many possible predecessors
              for (auto &elem : iInfo.iPred[&I]) {
                modified |= (dfa.in[&I] |= dfa.out[elem]);
              }
            }
            else { // Instruction in body of BB 
              if (pred != NULL) {
                modified |= (dfa.in[&I] |= dfa.out[pred]);
              }
            }

            // OUT = GEN union (IN - KILL)
            modified |= (dfa.out[&I] |= ((dfa.in[&I] - dfa.kill[&I]) | dfa.gen[&I]));

            pred = &(*iIter);
          }
        }
      }
    }

    void printDFA(InstrInfo &iInfo, DFAInfo &dfa) {
      errs() << "START FUNCTION: " << iInfo.F->getName() << "\n";
      for (unsigned i = 0; i < iInfo.instructions.size(); ++i) {
        errs() << "INSTRUCTION: ";
        Instruction *I = iInfo.instructions[i];
        I->print(errs());
        errs() << "\n";
        //printSet(dfa.gen[I], "GEN", instructions);
        //printSet(dfa.kill[I], "KILL", instructions);
        printSet(dfa.in[I], "IN", iInfo.instructions);
        printSet(dfa.out[I], "OUT", iInfo.instructions);
        errs() << "\n\n\n";
      }
    }

    Value* getPHINodeConstant(Instruction* reachingInst) {
      Value* PHIconstant = NULL;

      for (int op = 0; op < reachingInst->getNumOperands(); ++op) {
        bool validOp = false;
        Instruction* opI = (Instruction*)(reachingInst->getOperand(op));

        if (auto* opCall = dyn_cast<CallInst>(opI)) {
          if (opCall->getCalledFunction() == create_fn) {
            Value* constant = opCall->getArgOperand(0);
            if (auto* constantInt = dyn_cast<ConstantInt>(constant)) {
              if (PHIconstant == NULL) {
                validOp = true;
                PHIconstant = constant;
              } else if (constantInt->getSExtValue() == ((ConstantInt*)PHIconstant)->getSExtValue()) {
                validOp = true;
              }
            }
          }
        }

        if (!validOp) {
          //errs() << "Conflicting PHINode constant values\n";
          return NULL;
        }
      }

      return PHIconstant;
    }

    Value* getCATCreateConstant(CallInst* reachingCall) {
      for (auto& U : reachingCall->uses()) {
        Instruction* user = (Instruction*)(U.getUser());
        if (auto* store = dyn_cast<StoreInst>(user)) {
          Value* valStored = store->getValueOperand();
          if (auto* call = dyn_cast<CallInst>(valStored)) {
            if (call->getCalledFunction() == create_fn) {
              //errs() << "Escaping CAT_create in store\n";
              return NULL;
            }
          }
        }
      }

      Value* constant = reachingCall->getArgOperand(0);
      if (!isa<ConstantInt>(constant)) {
        //errs() << "Non constant CAT_create\n";
        return NULL;
      }
      return constant;
    }

    void decideToPropogate(InstrInfo &iInfo, DFAInfo &dfa, map<CallInst*, Value*> &constantCAT) {
      for (auto call : dfa.get_instrs) {
        call->print(errs());
        errs() << "\n";
        Instruction* CAT_read = (Instruction*)(call->getArgOperand(0));

        errs() << "IN SET:\n";
        for (auto elem : dfa.in[call]) {
          Instruction* reachingInst = iInfo.instructions[elem];

          iInfo.instructions[elem]->print(errs());
          errs() << "\n";
          
          Value* constant = NULL;
          bool validConstant = false;

          if (CAT_read == reachingInst) {
            if (isa<PHINode>(reachingInst)) {
              constant = getPHINodeConstant(reachingInst);
            } else if (auto* reachingCall = dyn_cast<CallInst>(reachingInst)) {
              Function *reachingFn = reachingCall->getCalledFunction();
              if (reachingFn == create_fn) {
                constant = getCATCreateConstant(reachingCall);
              }
            }
          } else {
            bool irrelevantInstr = false;
            switch(dfa.aa->alias(CAT_read, reachingInst)) {
              case NoAlias:
                errs() << "No alias; can ignore this IN set instruction\n";
                irrelevantInstr = true;
                break;
              case MayAlias:
              case PartialAlias:
                break;
              case MustAlias:
                errs() << "Must alias; check if is constant\n";
                if (auto* reachingCall = dyn_cast<CallInst>(reachingInst)) {
                  Function *reachingFn = reachingCall->getCalledFunction();
                  if (reachingFn == create_fn) {
                    constant = getCATCreateConstant(reachingCall);
                  }
                }
                break;
              default:
                abort();
            }
            if (irrelevantInstr)
              continue;
          }

          if (constantCAT.find(call) != constantCAT.end() && constant != NULL) {
            // Need to check for NULL constantCAT value
            if (((ConstantInt*)constant)->getSExtValue() == ((ConstantInt*)(constantCAT[call]))->getSExtValue()) {
              validConstant = true;
            }
          } else {
            validConstant = (constant != NULL);
          }

          if (!validConstant) {
            errs() << "Not propogating\n";
            constantCAT[call] = NULL;
            break;
          } else {
            errs() << "Adding constant to propogate\n";
            constant->print(errs());
            errs() << "\n";
            constantCAT[call] = constant;
          }
        }
        errs() << "END IN SET\n";
      }
    }

    bool doConstantPropogation(InstrInfo &iInfo, DFAInfo &dfa) {
      bool changesMade = false;
      map<CallInst*, Value*> constantCAT;

      decideToPropogate(iInfo, dfa, constantCAT);
    
      for (auto iter = constantCAT.begin(); iter != constantCAT.end(); ++iter) {
        if (iter->second != NULL) {
          //errs() << "REPLACING FOR THIS\n";
          CallInst* call = iter->first;
          BasicBlock::iterator ii(call);
          ReplaceInstWithValue(call->getParent()->getInstList(), ii, iter->second);
          changesMade = true;
        }
      }
      return changesMade;
    }

    void printSet(SparseBitVector<> &SET, string name, vector<Instruction*> instructions) {
      errs() << "***************** " << name << "\n{\n";
      for (auto elem : SET) {
        errs() << " " << *(instructions[elem]) << "\n";
      }
      errs() << "}\n**************************************\n";
      return;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      //errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      //AU.setPreservesAll();

      AU.addRequired<AAResultsWrapperPass>();
      return;
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
