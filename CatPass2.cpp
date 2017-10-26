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
      //SparseBitVector<> gen, kill;
      std::vector<Instruction *> gen, kill;
      std::string set_names[2] = { "GEN", "KILL" };
      auto sets = { &gen, &kill };

      errs() << "START FUNCTION: " << F.getName() << "\n";
      for (auto& B : F) {
        for (auto& I : B) {
          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function *callee;
            callee = call->getCalledFunction();  
            if (create_fn == callee || add_fn == callee || sub_fn == callee) {
              gen.push_back(&I);

              if (create_fn == callee) {
                for (auto& U : call->uses()) {
                  Instruction* user = (Instruction*)(U.getUser());
                  if (auto* userCall = dyn_cast<CallInst>(user)) {
                    Function* CAT_fn = userCall->getCalledFunction();
                    if ((CAT_fn == add_fn || CAT_fn == sub_fn) && 
                        U.getOperandNo() == 0) {
                      kill.push_back(user);
                    }
                  }
                }
              } else {
                Instruction *original_def = (Instruction*)(call->getArgOperand(0));
                kill.push_back(original_def);

                for (auto& U : call->getArgOperand(0)->uses()) {
                  Instruction* user = (Instruction*)(U.getUser());
                  if (auto* userCall = dyn_cast<CallInst>(user)) {
                    Function* CAT_fn = userCall->getCalledFunction();
                    if ((CAT_fn == add_fn || CAT_fn == sub_fn) && 
                        U.getOperandNo() == 0 && user != &I) {
                      kill.push_back(user);
                    }
                  }
                }
              }
            }
          }
          
          errs() << "INSTRUCTION: ";
          I.print(errs());
          errs() << "\n";

          int set_counter = 0;
          for (auto set : sets) {
            errs() << "***************** ";
            errs() << set_names[set_counter++] << "\n{\n";

            for (auto I_of_set : *set) {
              errs() << " ";
              I_of_set->print(errs());
              errs() << "\n";
            }
            errs() << "}\n**************************************\n";
          }
          errs() << "\n\n\n";

          gen.clear();
          kill.clear();
        }
      }
      return false;
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
