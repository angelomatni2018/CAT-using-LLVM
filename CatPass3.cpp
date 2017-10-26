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

#include <vector>
#include <map>
#include <set>

using namespace std;
using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 
    Function* create_fn;
    Function* add_fn;
    Function* sub_fn;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      //errs() << "Hello LLVM World at \"doInitialization\"\n" ;
    
      create_fn = M.getFunction("CAT_create_signed_value");
      add_fn = M.getFunction("CAT_binary_add");
      sub_fn = M.getFunction("CAT_binary_sub");

      return false;
    }

    // This function is invoked once per module compiled
    virtual bool runOnFunction (Function &F) {
      vector< Instruction* > instructions;
      map<Instruction*, int> instrIndices;
      map<Instruction*, SparseBitVector<>> gen, kill;
      map<Instruction*, set<Instruction*>> iPred; 
      unsigned counter = 0;

      for (auto &B : F) {
        TerminatorInst *terminatorInst = B.getTerminator();
        unsigned numSucc = terminatorInst->getNumSuccessors();
        for (auto i = 0; i < numSucc; ++i){
          BasicBlock *succ = terminatorInst->getSuccessor(i);
          Instruction *succI = &(succ->front());
          if (iPred.find(succI) == iPred.end())
            iPred[succI] = set<Instruction*>();
          iPred[succI].insert(terminatorInst);
        }

        for (auto &I : B) {
          instructions.push_back(&I);
          instrIndices[&I] = counter;
          ++counter;
        }
      }
      
      errs() << "START FUNCTION: " << F.getName() << "\n";
      counter = 0;
      // GEN, KILL, and instructions
      for (auto &B : F) {
        for (auto &I : B) {
          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();  
            if (create_fn == callee || add_fn == callee || sub_fn == callee) {
              gen[&I].set(counter);

              if (create_fn == callee) {
                for (auto& U : call->uses()) {
                  Instruction* user = (Instruction*)(U.getUser());
                  if (auto* userCall = dyn_cast<CallInst>(user)) {
                    Function* CAT_fn = userCall->getCalledFunction();
                    if ((CAT_fn == add_fn || CAT_fn == sub_fn) && U.getOperandNo() == 0) {
                      kill[&I].set(instrIndices[user]);
                    }
                  }
                }
              } else {
                Instruction *original_def = (Instruction*)(call->getArgOperand(0));
                kill[&I].set(instrIndices[original_def]);

                for (auto& U : call->getArgOperand(0)->uses()) {
                  Instruction* user = (Instruction*)(U.getUser());
                  if (auto* userCall = dyn_cast<CallInst>(user)) {
                    Function* CAT_fn = userCall->getCalledFunction();
                    if ((CAT_fn == add_fn || CAT_fn == sub_fn) && U.getOperandNo() == 0 && user != &I) {
                      kill[&I].set(instrIndices[user]);
                    }
                  }
                }
              }
            }
          }
          ++counter;
        }
      }

      map<Instruction*, SparseBitVector<>> in, out;
      // loop until convergence
      bool modified = true;
      while (modified) {
        modified = false;

        // Loop forwards through instructions
        for (auto bbIter = F.getBasicBlockList().begin(); bbIter != F.getBasicBlockList().end(); ++bbIter) {
          Instruction *pred = NULL;
          for (auto iIter = bbIter->begin(); iIter != bbIter->end(); ++iIter) {
            Instruction &I = *iIter;

            // IN = union of predecessor OUT
            if (iPred.count(&I)) { // Front with many possible predecessors
              for (auto &elem : iPred[&I]) {
                modified |= (in[&I] |= out[elem]);
              }
            }
            else { // Instruction in body of BB 
              if (pred != NULL) {
                modified |= (in[&I] |= out[pred]);
              }
            }

            // OUT = GEN union (IN - KILL)
            modified |= (out[&I] |= ((in[&I] - kill[&I]) | gen[&I]));

            pred = &(*iIter);
          }
        }
      }

      for (unsigned i = 0; i < instructions.size(); ++i) {
        errs() << "INSTRUCTION: ";
        Instruction *I = instructions[i];
        I->print(errs());
        errs() << "\n";
        //printSet(gen[I], "GEN", instructions);
        //printSet(kill[I], "KILL", instructions);
        printSet(in[I], "IN", instructions);
        printSet(out[I], "OUT", instructions);
        errs() << "\n\n\n";
      }

      return false;
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
      AU.setPreservesAll();
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
