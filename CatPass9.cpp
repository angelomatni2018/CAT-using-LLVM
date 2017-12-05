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
#include <stack>

using namespace std;
using namespace llvm;

namespace {
  enum CATType { CATCreate, CATGet, CATUpdate, CATPhi, FuncCall };

  struct InstrInfo {
    Function* F;
    map<BasicBlock*, set<BasicBlock*>> predB;
    map<BasicBlock*, set<BasicBlock*>> succB;
    map<BasicBlock*, vector<int>> bbI;
    vector<Instruction*> instructions;
    vector<CATType> instrTypes;
    
    map<Instruction*, int> instrIndices;
    vector<int> createI, getI, phiI;
    vector<StoreInst*> stores;
  };

  struct DFAInfo {
    map<BasicBlock*, SparseBitVector<>> genB, killB, inB, outB;
    map<int, SparseBitVector<>> gen, kill, in, out;
    AAResults* aa;
    map<int, set<int>> mayAliases;
    map<int, set<int>> mustAliases;
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

    bool doInitialization (Module &M) override {
      create_fn = M.getFunction("CAT_create_signed_value");
      get_fn = M.getFunction("CAT_get_signed_value");
      add_fn = M.getFunction("CAT_binary_add");
      sub_fn = M.getFunction("CAT_binary_sub");

      return false;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
      return;
    }

    bool runOnModule(Module &M) override {
      bool changed = false;
      for (auto &F : M) {
        if (F.empty()) 
          continue;
        changed |= passOnFunction(F);
      }
      return changed;
    }

    bool passOnFunction(Function &F) {
      dfa = new DFAInfo();
      iInfo = new InstrInfo();

      iInfo->F = &F;
      dfa->aa = &(getAnalysis<AAResultsWrapperPass>(F).getAAResults());

      collectInstrInfo();
      markAliases();
      computeGenKill();
      computeInOut();

      //errs() << "\n\nSTART DFA PRINT\n\n";
      //printDFAb();
      //printDFA();

      bool changed = doConstantPropogation();
      free(dfa);
      free(iInfo);
      return changed;
    }

    bool isCAT(Function* F) {
      return F == add_fn || F == sub_fn || F == get_fn || F == create_fn;
    }
    
    void collectInstrInfo() {
      unsigned numI = 0;
      for (auto &B : *(iInfo->F)) {
        iInfo->predB[&B] = set<BasicBlock*>();
        iInfo->succB[&B] = set<BasicBlock*>();
        iInfo->bbI[&B] = vector<int>();
      }
      for (auto &B : *(iInfo->F)) {
        TerminatorInst *terminatorInst = B.getTerminator();
        for (auto i = 0; i < terminatorInst->getNumSuccessors(); ++i) {
          iInfo->succB[&B].insert(terminatorInst->getSuccessor(i));
          iInfo->predB[terminatorInst->getSuccessor(i)].insert(&B);
        }
        for (auto &I : B) {
          bool logInstr = false;
          if (auto* call = dyn_cast<CallInst>(&I)) {
            Function* callee = call->getCalledFunction();
            // Pertinent if CAT api or defined locally
            if (isCAT(callee) || !callee->empty()) {
              logInstr = true;
              if (callee == create_fn) {
                iInfo->instrTypes.push_back(CATCreate);
                iInfo->createI.push_back(numI);
              } else if (callee == get_fn) {
                iInfo->instrTypes.push_back(CATGet);
                iInfo->getI.push_back(numI);
              } else if (callee == add_fn || callee == sub_fn) {
                iInfo->instrTypes.push_back(CATUpdate);
              } else {
                iInfo->instrTypes.push_back(FuncCall);
              }
            }
          } else if (auto* store = dyn_cast<StoreInst>(&I)) {
            if (auto* call = dyn_cast<CallInst>(store->getValueOperand())) {
              if (call->getCalledFunction() == create_fn) {
                iInfo->stores.push_back(store);
              }
            }
          } else if (auto* phi = dyn_cast<PHINode>(&I)) {
            for (auto i = 0; i < phi->getNumIncomingValues(); ++i) {
              //errs() << "Phi arg: " << i << " for\t" << *phi << "\n";
              if (auto* phiOp = dyn_cast<CallInst>(phi->getIncomingValue(i))) {
                if (phiOp->getCalledFunction() == create_fn) {
                  //errs() << "\tIt is create\n";
                  logInstr = true;
                  iInfo->instrTypes.push_back(CATPhi);
                  iInfo->phiI.push_back(numI);
                  break;
                }
              }
            }
          }

          if (logInstr) {
            iInfo->instructions.push_back(&I);
            iInfo->instrIndices[&I] = numI;
            iInfo->bbI[&B].push_back(numI);
            ++numI;
          }
        }
      }
    }

    void markAlias(map<int, set<int>> &aliases, int alias1, int alias2) {
      if (aliases.find(alias1) == aliases.end())
        aliases[alias1] = set<int>();
      //errs() << "Marked " << alias1 << " onto " << alias2 << "\n";
      aliases[alias1].insert(alias2);
      if (aliases.find(alias2) == aliases.end())
        aliases[alias2] = set<int>();
      aliases[alias2].insert(alias1);
      //errs() << "Marked " << alias2 << " onto " << alias1 << "\n";
    }

    bool modRefd(ModRefInfo info) {
      return info == MRI_Ref || info == MRI_Mod || info == MRI_ModRef;
    }

    void markAliases() {
      for (auto i = 0; i < iInfo->instructions.size(); i++) {
        //errs() << "Instruction " << i << " " << iInfo->instrTypes[i] << "\n";
        switch (iInfo->instrTypes[i]) {
          case CATUpdate:
          {
            CallInst *I = (CallInst*)(iInfo->instructions[i]);
            //I->print(errs() << "Alias For:\t");
            //errs() << "\n";
            Value* argI = I->getArgOperand(0);
            //argI->print(errs() << "Arg:\t");
            //errs() << "\n";
            if (auto* load = dyn_cast<LoadInst>(argI)) {
              for (auto s = 0; s < iInfo->stores.size(); s++) {
                StoreInst* store = iInfo->stores[s];
                Instruction* cat = (Instruction*)(store->getValueOperand());
                int catInd = iInfo->instrIndices[cat];
                //store->print(errs() << "Checking:\t");
                //errs() << "\n";
                switch (dfa->aa->alias(MemoryLocation::get(load), MemoryLocation::get(store))) {
                  case PartialAlias:
                  case MayAlias:
                    markAlias(dfa->mayAliases, i, catInd);
                    break;
                  case MustAlias:
                    markAlias(dfa->mustAliases, i, catInd);
                    break;
                }
              }
            }
          }
            break;
          case FuncCall:
          {
            CallInst *I = (CallInst*)(iInfo->instructions[i]);
            //I->print(errs() << "Alias For:\t");
            //errs() << "\n";
            for (int op = 0; op < I->getNumOperands(); ++op) {
              Instruction* opI = (Instruction*)(I->getOperand(op));
              auto it = iInfo->instrIndices.find(opI);
              if (it == iInfo->instrIndices.end())
                continue;
              int opInd = it->second;
              switch (iInfo->instrTypes[opInd]) {
                case CATPhi:
                {
                  //opI->print(errs() << "Function arg:\t");
                  //errs() << "\n";
                  markAlias(dfa->mayAliases, i, opInd);
                  PHINode* opPhi = (PHINode*)opI;
                  for (int phi = 0; phi < opPhi->getNumIncomingValues(); ++phi) {
                    Instruction* phiI = (Instruction*)(opPhi->getIncomingValue(phi));
                    int phiInd = iInfo->instrIndices[phiI];
                    //phiI->print(errs() << "Phi arg:\t");
                    //errs() << "\n";
                    markAlias(dfa->mayAliases, i, phiInd);
                  }
                  break;
                }
                case CATCreate:
                  //opI->print(errs() << "Function arg:\t");
                  //errs() << "\n";
                  markAlias(dfa->mayAliases, i, opInd);
                  break;
              }
            }
            for (auto store : iInfo->stores) {
              //store->print(errs() << "Checking:\t");
              //errs() << "\n";
              if (modRefd(dfa->aa->getModRefInfo(I, MemoryLocation::get(store)))) {
                Instruction* cat = (Instruction*)(store->getValueOperand());
                int catInd = iInfo->instrIndices[cat];
                //cat->print(errs() << "Function modref'd:\t");
                //errs() << "\n";
                markAlias(dfa->mayAliases, i, catInd);
              }
            }
            break;
          }
        }
      }
    }

    void markKill(int I, Instruction* def) {
      auto it = iInfo->instrIndices.find(def);
      if (it != iInfo->instrIndices.end())
        dfa->kill[I].set(it->second);
    }
    
    void setKillFromUses(int I, Instruction* def) {
      for (auto& U : def->uses()) {
        Instruction* user = (Instruction*)(U.getUser());
        auto it = iInfo->instrIndices.find(user);
        if (it == iInfo->instrIndices.end())
          continue;
        switch (iInfo->instrTypes[it->second]) {
          case CATUpdate:
            if (U.getOperandNo() == 0 && it->second != I)
              markKill(I, user);
            break;
          case CATPhi:
            markKill(I, user);
            break;
        }
      }
    }

    void setKillFromAliases(int I, int aliaser) {
      if (dfa->mustAliases.find(aliaser) != dfa->mustAliases.end()) {
        for (auto alias : dfa->mustAliases[aliaser]) {
          Instruction* aliasI = iInfo->instructions[alias];
          markKill(I, aliasI);
          setKillFromUses(I, aliasI);
        }
      }
    }

    void computeGenKill() {
      for (int i = 0; i < iInfo->instructions.size(); ++i) {
        Instruction* I = iInfo->instructions[i];
        switch (iInfo->instrTypes[i]) {
          case CATCreate:
          case CATPhi:
            dfa->gen[i].set(i);
            setKillFromUses(i, I);
            setKillFromAliases(i, i);
            break;
          case CATUpdate:
          {
            dfa->gen[i].set(i);
            Instruction *def = (Instruction*)(((CallInst*)I)->getArgOperand(0));
            auto it = iInfo->instrIndices.find(def);
            markKill(i, def);
            setKillFromUses(i, def);
            setKillFromAliases(i, it->second);
            break;
          }
          case FuncCall:
            dfa->gen[i].set(i);
            break;
        }
      }
      for (auto b = iInfo->bbI.begin(); b != iInfo->bbI.end(); ++b) {
        BasicBlock* B = b->first;
        for (int i = b->second.size() - 1; i >= 0; i--) {
          int iInd = b->second[i];
          dfa->genB[B] |= dfa->gen[iInd] - dfa->killB[B];
          dfa->killB[B] |= dfa->kill[iInd] - dfa->genB[B];
        }
      }
    }
    
    void computeInOut() {
      stack<BasicBlock*> bbs;
      for (auto b = iInfo->bbI.begin(); b != iInfo->bbI.end(); ++b) {
        bbs.push(b->first);
      }
      while (!bbs.empty()) {
        BasicBlock* B = bbs.top();
        bbs.pop();
        for (auto pred : iInfo->predB[B]) {
          dfa->inB[B] |= dfa->outB[pred];
        }
        if (dfa->outB[B] |= ((dfa->inB[B] - dfa->killB[B]) | dfa->genB[B])) {
          for (auto succ : iInfo->succB[B]) {
            bbs.push(succ);
          }
        }
      }
      for (auto b = iInfo->bbI.begin(); b != iInfo->bbI.end(); ++b) {
        if (b->second.size() == 0)
          continue;
        int iInd = b->second[0];
        dfa->in[iInd] |= dfa->inB[b->first];
        dfa->out[iInd] |= ((dfa->in[iInd] - dfa->kill[iInd]) | dfa->gen[iInd]);
        for (int i = 1; i < b->second.size(); i++) {
          int iIndNew = b->second[i];
          dfa->in[iIndNew] |= dfa->out[iInd];
          dfa->out[iIndNew] |= ((dfa->in[iIndNew] - dfa->kill[iIndNew]) | dfa->gen[iIndNew]);
          iInd = iIndNew;
        }
      }
    }

    void printDFAb() {
      errs() << "START FUNCTION: " << iInfo->F->getName() << "\n";
      for (auto b = iInfo->bbI.begin(); b != iInfo->bbI.end(); ++b) {
        errs() << "BASIC BLOCK: ";
        BasicBlock *B = b->first;
        B->print(errs());
        errs() << "\n";
        printSet(dfa->genB[B], "GEN");
        printSet(dfa->killB[B], "KILL");
        printSet(dfa->inB[B], "IN");
        printSet(dfa->outB[B], "OUT");
        errs() << "\n\n\n";
      }
    }

    void printDFA() {
      errs() << "START FUNCTION: " << iInfo->F->getName() << "\n";
      for (unsigned i = 0; i < iInfo->instructions.size(); ++i) {
        errs() << "INSTRUCTION: ";
        Instruction *I = iInfo->instructions[i];
        I->print(errs());
        errs() << "\n";
        printSet(dfa->gen[i], "GEN");
        printSet(dfa->kill[i], "KILL");
        printSet(dfa->in[i], "IN");
        printSet(dfa->out[i], "OUT");
        errs() << "\n\n\n";
      }
    }

    void printSet(SparseBitVector<> &SET, string name) {
      errs() << "***************** " << name << "\n{\n";
      for (auto elem : SET) {
        errs() << " " << *(iInfo->instructions[elem]) << "\n";
      }
      errs() << "}\n**************************************\n";
      return;
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

    bool isInAlias(map<int, set<int>> &aliases, int alias1, int alias2) {
      if (aliases.find(alias1) == aliases.end()) 
        return false;
      auto* aliasSet = &(aliases[alias1]);
      return (aliasSet->find(alias2) != aliasSet->end());
    }

    void decideToPropogate(map<CallInst*, Value*> &constantCAT) {
      for (auto i : iInfo->getI) {
        CallInst* call = (CallInst*)(iInfo->instructions[i]);
        Instruction* getArg = (Instruction*)(call->getArgOperand(0));
        auto itArg = iInfo->instrIndices.find(getArg);
        if (itArg == iInfo->instrIndices.end())
          continue;

        int indArg = itArg->second;
        bool getArgReaches = false;
        bool updateReaches = false;
        Value* constant = NULL;
        switch (iInfo->instrTypes[indArg]) {
          case CATCreate:
            constant = getCATCreateConstant((CallInst*)getArg);
            break;
          case CATPhi:
            constant = getPHIConstants(getArg);
            break;
        }
        if (constant == NULL) 
          continue;
        for (auto elem : dfa->in[i]) {
          //errs() << "elem " << elem << " " << *(iInfo->instructions[elem]) <<"\n";
          if (elem == indArg) {
            //errs() << "Elem matches get arg\n";
            getArgReaches = true;
            continue;
          }
          switch (iInfo->instrTypes[elem]) {
            case CATUpdate:
            {
              CallInst* updateI = (CallInst*)(iInfo->instructions[elem]);
              Instruction* defI = (Instruction*)(updateI->getArgOperand(0));
              int indDef = iInfo->instrIndices.find(defI)->second;
              updateReaches |= (indDef == indArg || isInAlias(dfa->mayAliases, indArg, indDef));
              break;
            }
            case FuncCall:
              //errs() << "Alias check on:\t" << *(iInfo->instructions[elem]) << "\n";
              //errs() << "Alias check against:\t" << *getArg << "\n";
              updateReaches |= isInAlias(dfa->mayAliases, indArg, elem);
              //errs() << "Does alias: " << updateReaches << "\n";
              break;
          }
          if (updateReaches)
            break;
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