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

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/Statistic.h"

#include <vector>
#include <map>
#include <set>
#include <queue>

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
    map<Instruction*, set<Instruction*>> mayAliases;
    map<Instruction*, set<Instruction*>> mustAliases;
    map<Value*, set<StoreInst*>> pntStores;
    SparseBitVector<> escapedInstrs;
  };

  struct CAT : public ModulePass {
    static char ID; 
    Function* create_fn;
    Function* get_fn;
    Function* add_fn;
    Function* sub_fn;

    DFAInfo* dfa;
    InstrInfo* iInfo;

    CAT() : ModulePass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      create_fn = M.getFunction("CAT_create_signed_value");
      get_fn = M.getFunction("CAT_get_signed_value");
      add_fn = M.getFunction("CAT_binary_add");
      sub_fn = M.getFunction("CAT_binary_sub");

      return false;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired< CallGraphWrapperPass >();
      AU.addRequired<AAResultsWrapperPass>();
      return;
    }

    bool runOnModule(Module &M) override {
      CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
      
      bool changed = false;
      for (auto &F : M) {
        if (F.empty())
          continue;
        changed |= inlineFunction(CG, F);
      }

      if (changed)
        return true;

      for (auto &F : M) {
        if (F.empty()) 
          continue;
        changed |= passOnFunction(F);
      }
      return changed;
    }

    bool inlineFunction(CallGraph &CG, Function &F) {
      bool changed = false;
      CallGraphNode *n = CG[&F];

      for (auto callee : *n) {
        auto callVH = callee.first;
        if (!callVH)
          continue;
        if (auto* call = dyn_cast<CallInst>(callVH)) {
          // Don't inline recursive calls
          if (call->getCalledFunction() == &F)
            continue;
          // Don't inline functions with "many" refs
          if (callee.second->getNumReferences() > 2)
            continue;

          InlineFunctionInfo  IFI;
          bool inlined = InlineFunction(call, IFI);
          if (inlined) {
            changed = true;
            break;
          }
        }
      }

      if (changed)
        inlineFunction(CG, F);

      return changed;
    }

    bool passOnFunction(Function &F) {
      dfa = new DFAInfo();
      iInfo = new InstrInfo();

      iInfo->F = &F;
      dfa->aa = &(getAnalysis<AAResultsWrapperPass>(F).getAAResults());

      collectInstrInfo();
      markAliases();
      markEscapes();
      computeGenKill();
      computeInOut();

      //errs() << "\n\nSTART DFA PRINT\n\n";
      //printDFA();

      bool changed = doConstantPropogation();

      free(dfa);
      free(iInfo);

      return changed;
    }
    
    bool isCATUpdate(Function* F) {
      return F == add_fn || F == sub_fn;
    }

    bool isCAT(Function* F) {
      return isCATUpdate(F) || F == get_fn || F == create_fn;
    }

    void collectInstrInfo() {
      unsigned counter = 0;

      for (auto &B : *(iInfo->F)) {
        TerminatorInst *terminatorInst = B.getTerminator();
        unsigned numSucc = terminatorInst->getNumSuccessors();
        for (auto i = 0; i < numSucc; ++i){
          BasicBlock *succ = terminatorInst->getSuccessor(i);
          Instruction *succI = &(succ->front());
          if (iInfo->iPred.find(succI) == iInfo->iPred.end())
            iInfo->iPred[succI] = set<Instruction*>();
          iInfo->iPred[succI].insert(terminatorInst);
        }

        for (auto &I : B) {
          iInfo->instructions.push_back(&I);
          iInfo->instrIndices[&I] = counter;
          ++counter;
        }
      }
    }

    void markAlias(map<Instruction*, set<Instruction*>> &aliases,
        Instruction* alias1, Instruction* alias2) {
      if (aliases.find(alias1) == aliases.end())
        aliases[alias1] = set<Instruction*>();
      aliases[alias1].insert(alias2);
      if (aliases.find(alias2) == aliases.end())
        aliases[alias2] = set<Instruction*>();
      aliases[alias2].insert(alias1);
    }

    // Populates mayAlias and mustAlias maps for DFA
    void markAliases() {
      auto stores = set<StoreInst*>();
      for (auto I : iInfo->instructions) {
        if (auto* store = dyn_cast<StoreInst>(I)) {
          stores.insert(store);
        } else if (auto* load = dyn_cast<LoadInst>(I)) {
          for (auto store : stores) {
            bool may = false, must = false;

            switch (dfa->aa->alias(MemoryLocation::get(load), MemoryLocation::get(store))) {
              case NoAlias:
                break;
              case MayAlias:
                may = true;
                break;
              case PartialAlias:
                may = true;
                break;
              case MustAlias:
                must = true;
                break;
              default:
                abort();
            }
            if (may || must) {
              Instruction* cat = (Instruction*)(store->getValueOperand());
              Instruction* catLoad = (Instruction*)load;
              if (may) {
                markAlias(dfa->mayAliases, catLoad, cat);
              } else {
                markAlias(dfa->mustAliases, catLoad, cat);
              }
            }
          }
        }
      }
    }

    bool modRefd(ModRefInfo info) {
      switch(info) {
        case MRI_NoModRef:
          break;
        case MRI_Ref:
          return true;
        case MRI_Mod:
          return true;
        case MRI_ModRef:
          return true;
        default:
          abort();
      }
      return false;
    }

    void searchAndEscape(Value* opV) {
      queue<Value*> vals;
      Value* aliasedV;
      vals.push(opV);
      while (!vals.empty()) {
        opV = vals.front();
        vals.pop();

        for (auto store : dfa->pntStores[opV]) {
          aliasedV = store->getValueOperand();
          if (auto* aliasedCall = dyn_cast<CallInst>(aliasedV)) {
            if (aliasedCall->getCalledFunction() == create_fn) {
              dfa->escapedInstrs.set(iInfo->instrIndices[(Instruction*)aliasedV]);
            }
          } else if (isa<PHINode>(aliasedV)) {
            dfa->escapedInstrs.set(iInfo->instrIndices[(Instruction*)aliasedV]);
          } else if (dfa->pntStores.find(aliasedV) != dfa->pntStores.end()) {
            vals.push(aliasedV);
          }
        }
      }
    }

    // Conservatively escapes CAT creates and phiNodes if Ref, Mod, or ModRef
    void markEscapes() {
      for (auto I : iInfo->instructions) {
        if (auto* store = dyn_cast<StoreInst>(I)) {
          Value* pntStore = store->getPointerOperand();

          if (dfa->pntStores.find(pntStore) == dfa->pntStores.end())
            dfa->pntStores[pntStore] = set<StoreInst*>();
          dfa->pntStores[pntStore].insert(store);
        } else if (auto* call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();  
          if (isCAT(callee))
            continue;

          for (int op = 0; op < I->getNumOperands(); ++op) {
            Value* opV = I->getOperand(op);

            if (auto* opCall = dyn_cast<CallInst>(opV)) {
              if (opCall->getCalledFunction() == create_fn) {
                if (modRefd(dfa->aa->getModRefInfo(call, opCall))) {
                  dfa->escapedInstrs.set(iInfo->instrIndices[(Instruction*)opV]);
                }
              }
            } else if (isa<PHINode>(opV)) {
              dfa->escapedInstrs.set(iInfo->instrIndices[(Instruction*)opV]);
            }

            if (dfa->pntStores.find(opV) == dfa->pntStores.end())
              continue;

            for (auto store : dfa->pntStores[opV]) {
              if (modRefd(dfa->aa->getModRefInfo(call, MemoryLocation::get(store)))) {
                // Search to escape CAT creates and phiNodes
                searchAndEscape(opV);
              }
            }
          }
        }
      }
    }

    void markKill(Instruction* I, Instruction* def) {
      if (iInfo->instrIndices.find(def) != iInfo->instrIndices.end())
        dfa->kill[I].set(iInfo->instrIndices[def]);
    }

    void setKillFromUses(Instruction* I, Instruction* def) {
        for (auto& U : def->uses()) {
          Instruction* user = (Instruction*)(U.getUser());
          if (auto* userCall = dyn_cast<CallInst>(user)) {
            Function* CAT_fn = userCall->getCalledFunction();
            if (isCATUpdate(CAT_fn) && U.getOperandNo() == 0 && user != I) {
              markKill(I, user);
            }
          } else if (isa<PHINode>(user)) {
            markKill(I, user);
          }
        }
    }

    void setKillFromAliases(Instruction* I, Instruction* aliaser) {
      if (dfa->mustAliases.find(aliaser) != dfa->mustAliases.end()) {
        for (auto aliasI : dfa->mustAliases[aliaser]) {
          markKill(I, aliasI);
          setKillFromUses(I, aliasI);
        }
      }
    }

    void computeGenKill() {
      unsigned counter = 0;
      // GEN, KILL, and instructions
      for (auto &B : *(iInfo->F)) {
        for (auto &I : B) {
          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();  
            if (create_fn == callee) {
              dfa->gen[&I].set(counter);
              
              setKillFromUses(&I, &I);
              setKillFromAliases(&I, &I);
            } else if (isCATUpdate(callee)) {
              dfa->gen[&I].set(counter);

              Instruction *def = (Instruction*)(call->getArgOperand(0));
              if (auto* create_def = dyn_cast<CallInst>(def)) {
                if (create_def->getCalledFunction() == create_fn) {
                  markKill(&I, def);
                  setKillFromUses(&I, def);
                  setKillFromAliases(&I, def);
                } else {
                  // Function returning CATData not meaningful due to conservativeness
                }
              } else if (auto* load_def = dyn_cast<LoadInst>(def)) {
                setKillFromUses(&I, def);
                setKillFromAliases(&I, def);
              }
            } else if (get_fn == callee) {
              dfa->get_instrs.push_back(call);
            }
          } else if (isa<PHINode>(&I)) {
            dfa->gen[&I].set(counter);

            setKillFromUses(&I, &I);
            setKillFromAliases(&I, &I);
          }
          ++counter;
        }
      }
    }

    void computeInOut() {
      // loop until convergence
      bool modified = true;
      while (modified) {
        modified = false;

        // Loop forwards through instructions
        for (auto bbIter = iInfo->F->getBasicBlockList().begin(); bbIter != iInfo->F->getBasicBlockList().end(); ++bbIter) {
          Instruction *pred = NULL;
          for (auto iIter = bbIter->begin(); iIter != bbIter->end(); ++iIter) {
            Instruction &I = *iIter;

            // IN = union of predecessor OUT
            if (iInfo->iPred.count(&I)) { // Front with many possible predecessors
              for (auto &elem : iInfo->iPred[&I]) {
                modified |= (dfa->in[&I] |= dfa->out[elem]);
              }
            }
            else { // Instruction in body of BB 
              if (pred != NULL) {
                modified |= (dfa->in[&I] |= dfa->out[pred]);
              }
            }

            // OUT = GEN union (IN - KILL)
            modified |= (dfa->out[&I] |= ((dfa->in[&I] - dfa->kill[&I]) | dfa->gen[&I]));

            pred = &(*iIter);
          }
        }
      }
    }

    void printDFA() {
      errs() << "START FUNCTION: " << iInfo->F->getName() << "\n";
      for (unsigned i = 0; i < iInfo->instructions.size(); ++i) {
        errs() << "INSTRUCTION: ";
        Instruction *I = iInfo->instructions[i];
        I->print(errs());
        errs() << "\n";
        //printSet(dfa->gen[I], "GEN", instructions);
        //printSet(dfa->kill[I], "KILL", instructions);
        printSet(dfa->in[I], "IN", iInfo->instructions);
        printSet(dfa->out[I], "OUT", iInfo->instructions);
        errs() << "\n\n\n";
      }
    }

    Value* getCATCreateConstant(CallInst* reachingCall) {
      Value* constant = reachingCall->getArgOperand(0);
      if (!isa<ConstantInt>(constant))
        return NULL;
      return constant;
    }

    Value* getPHIConstants(Instruction* phi) {
      ConstantInt* constant = NULL;

      for (int op = 0; op < phi->getNumOperands(); ++op) {
        Instruction* opI = (Instruction*)(phi->getOperand(op));

        if (auto* opCall = dyn_cast<CallInst>(opI)) {
          if (opCall->getCalledFunction() == create_fn) {
            Value* constV = opCall->getArgOperand(0);
            if (auto* constI = dyn_cast<ConstantInt>(constV)) {
              if (constant == NULL) {
                constant = constI;
                continue;
              } else if (constI->getSExtValue() == constant->getSExtValue()) {
                continue;
              }
            }
          }
        }

        return NULL;
      }

      return (Value*)constant;
    }

    bool isInAlias(map<Instruction*, set<Instruction*>> &aliases,
        Instruction* alias1, 
        Instruction* alias2) {
      if (aliases.find(alias1) == aliases.end()) 
        return false;
      auto* aliasSet = &(aliases[alias1]);
      return (aliasSet->find(alias2) != aliasSet->end());
    }

    void decideToPropogate(map<CallInst*, Value*> &constantCAT) {
      for (auto call : dfa->get_instrs) {
        Instruction* getArg = (Instruction*)(call->getArgOperand(0));
        Value* constant = NULL;
        bool getArgReaches = false;
        bool updateReaches = false;

        if (auto* getCall = dyn_cast<CallInst>(getArg)) {
          if (getCall->getCalledFunction() == create_fn) {
            constant = getCATCreateConstant(getCall);
          }
        } else if (isa<PHINode>(getArg)) {
          constant = getPHIConstants(getArg);
        }

        if (constant == NULL) 
          continue;
        if (dfa->escapedInstrs.test(iInfo->instrIndices[getArg]))
          continue;

        for (auto elem : dfa->in[call]) {
          Instruction* reachingInst = iInfo->instructions[elem];

          if (reachingInst == getArg)
            getArgReaches = true;

          if (auto* reachingCall = dyn_cast<CallInst>(reachingInst)) {
            Function *callee = reachingCall->getCalledFunction();

            if (isCATUpdate(callee)) {
              Instruction* def = (Instruction*)(reachingCall->getArgOperand(0));
              if (isInAlias(dfa->mayAliases, getArg, def)) {
                updateReaches = true;
                break;
              }
            }
          }
        }
        
        if (!getArgReaches || updateReaches) 
          continue;

        constantCAT[call] = constant;
      }
    }

    bool doConstantPropogation() {
      bool changesMade = false;
      map<CallInst*, Value*> constantCAT;

      decideToPropogate(constantCAT);
    
      for (auto iter = constantCAT.begin(); iter != constantCAT.end(); ++iter) {
        if (iter->second != NULL) {
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
