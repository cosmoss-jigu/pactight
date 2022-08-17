// DVIPACPass.h - DVI-PAC project - COSMOSS
//
//
// Author: Mohannad Ismail

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
/*
// String references for the functions.
llvm::StringRef INITMEMORY("init_memory");
llvm::StringRef ADDPAC("addPAC");
llvm::StringRef AUTHPAC("authenticatePAC");
llvm::StringRef ADDPACNULL("addPACNull");
llvm::StringRef AUTHPACNULL("authenticatePACNull");
llvm::StringRef SETMETA("setMetadata");
llvm::StringRef SETMETAOBJ("setMetadataObj");
llvm::StringRef REMOVEMETA("removeMetadata");
llvm::StringRef REMOVEMETASTACK("removeMetadataStack");
llvm::StringRef METAEXISTS("metadataExists");
*/
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

	ModulePass *createDVIPACPass();
}
