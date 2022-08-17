// InitDVIPACPass.h - DVI-PAC project - COSMOSS
//
//
// Author: Mohannad Ismail

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

namespace llvm {
	
	struct InlineParams;
	class StringRef;
	class ModuleSummaryIndex;
	class ModulePass;
	class Pass;
	class Function;
	class BasicBlock;
	class GlobalValue;
	class raw_ostream;

	ModulePass *createInitDVIPACPass();
}
