#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/IR/LegacyPassManager.h"

#include <map>

using namespace llvm;

namespace {
  struct CAT : public ModulePass {
    static char ID; 

    CAT() : ModulePass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      //errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      return false;
    }

    // This function is invoked once per module compiled
    virtual bool runOnModule (Module &M) {
      for (Function &F : M) {
        std::map<std::string,int> CAT_fns;
        CAT_fns["CAT_binary_add"] = 0;
        CAT_fns["CAT_binary_sub"] = 0;
        CAT_fns["CAT_create_signed_value"] = 0;
        CAT_fns["CAT_get_signed_value"] = 0;

        auto it = CAT_fns.find(F.getName());
        // Don't run for functions we are counting up
        if (it != CAT_fns.end()) {
          continue;
        }

        for (auto& B : F) {
          for (auto& I : B) {
            if (auto* call = dyn_cast<CallInst>(&I)) {
              Function *callee;

              callee = call->getCalledFunction();
              
              auto it = CAT_fns.find(callee->getName());
              if (it != CAT_fns.end()) {
                CAT_fns[it->first] += 1;
              }
            }
          }
        }

        for (auto it = CAT_fns.begin(); it != CAT_fns.end(); ++it) {
          if (it->second == 0)
            continue;
          errs() << "H1: " << '"' << F.getName() << '"' << ": "; 
          errs() << it->first << ": ";
          errs() << it->second << "\n";
          CAT_fns[it->first] = 0;
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
