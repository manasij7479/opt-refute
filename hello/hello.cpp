#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Evaluator.h"
#include "llvm/Transforms/Utils/Cloning.h"


#include <string>
#include <unordered_set>

using namespace llvm;

static cl::opt<std::string> LHSName("lhs", cl::desc("Name of LHS function to test"), cl::value_desc("function"), cl::Required);

namespace {
class RefuteOpts : public llvm::ModulePass {
public:
  static char ID;
  RefuteOpts() : ModulePass(ID) {}


  bool runOnModule(llvm::Module & M) override {

    auto&& zero = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, 0, false));
    llvm::SmallVector<llvm::Constant *, 2> args = {zero};
    TryRefute(args, M);

    auto&& wut = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, 7479, false));
    args = {wut};
    TryRefute(args, M);

    wut = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, 45, false));
    args = {wut};
    TryRefute(args, M);

    wut = llvm::ConstantInt::get(M.getContext(), llvm::APInt(32, -1, false));
    args = {wut};
    TryRefute(args, M);

    llvm::outs() << "Proved " << refuted.size() << "/" << M.getFunctionList().size() << " functions infeasible.";
  }
private:

  void TryRefute(llvm::SmallVector<llvm::Constant *, 2> args, llvm::Module & M) {
    auto&& LHS = M.getFunction(LHSName);

    assert(LHS->arg_size() == 1 && "Only supports LHS with one args so far");
    // TODO Get rid of this limitation

    llvm::Evaluator eval(M.getDataLayout(), nullptr);

    llvm::Constant *C;
    auto couldEvaluate = eval.EvaluateFunction(LHS, C, args);

    for (auto&& F : M.getFunctionList()) {
      if (IsRHSInfeasible(C, args, &F, M)) {
        refuted.insert(&F);
      }
    }

  }

  bool IsRHSInfeasible(llvm::Constant *LHS,
                       llvm::SmallVector<llvm::Constant *, 2> args,
                       llvm::Function *RHS,
                       llvm::Module &M) {
    if (refuted.find(RHS) != refuted.end()) {
      return false;
    }

    llvm::ValueToValueMapTy map;
    int i = 0;
    for (auto&& arg : RHS->args()) {
      if (i == 0) {
        map[&arg] = args[0]; // first i32 arg generated bu opt-fuzz
      }
//       if (i == 4) {
//         map[&arg] = args[4]; // second i32 arg generated bu opt-fuzz
//       }
      i++;
    }

    auto NewF = llvm::CloneFunction(RHS, map);

    int ConstantIntValue;
    if (ConstantInt* CI = dyn_cast<ConstantInt>(LHS)) {
      if (CI->getBitWidth() <= 32) {
        ConstantIntValue = CI->getSExtValue();
      }
    }
    for (auto &BB : *NewF) {
      for (auto &I : BB) {
        if (I.getOpcode() == Instruction::Ret) {
          KnownBits Known = computeKnownBits(I.getOperand(0), M.getDataLayout());
          if ((Known.Zero & ConstantIntValue) != 0 || (Known.One & ~ConstantIntValue) != 0) {
            NewF->removeFromParent();
            return true;
          }
        }
      }
    }

    NewF->removeFromParent();
    return false;
  }

  std::unordered_set<llvm::Function *> refuted;
};

}  // end of anonymous namespace

char RefuteOpts::ID = 0;
static RegisterPass<RefuteOpts> X("refute", "opt-refute pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
