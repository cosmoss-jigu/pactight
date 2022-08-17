// DVIPACPass.cpp - DVI-PAC project - COSMOSS
//
//
// Author: Mohannad Ismail

#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/CtorUtils.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/ValueHandle.h"

#include <cstdint>
#include <utility>
#include <vector>
#include <tuple>
#include <unordered_map>

//#define CPS

using namespace llvm;
using std::unordered_map;
using std::make_pair;
using std::make_tuple;
//using namespace std;
using std::vector;
using std::get;
//using std::string;
using std::tuple;
using std::pair;


// String references for the functions.
StringRef INITMEMORY1("init_memory");
StringRef ADDPAC1("addPAC");
StringRef AUTHPAC1("authenticatePAC");
StringRef ADDPACNULL1("addPACNull");
StringRef AUTHPACNULL1("authenticatePACNull");
StringRef SETMETA1("setMetadata");
StringRef SETMETAOBJ1("setMetadataObj");
StringRef REMOVEMETA1("removeMetadata");
StringRef REMOVEMETASTACK1("removeMetadataStack");
StringRef METAEXISTS1("metadataExists");


// Statistics regarding instructions and to count number of times each function is instrumented.
#define DEBUG_TYPE "InitDVIPACPass"
STATISTIC(addPAC_count, "Number of addPAC functions.");
STATISTIC(authPAC_count, "Number of authenticatePAC functions.");
STATISTIC(setMeta_count, "Number of setMetadata functions.");
STATISTIC(removeMeta_count, "Number of removeMetadata functions.");
STATISTIC(numStores, "Number of memory stores.");
STATISTIC(numPACStores, "Number of memory stores protected with DVI-PAC.");
STATISTIC(numLoads, "Number of memory loads.");
STATISTIC(numPACLoads, "Number of memory loads protected with DVI-PAC.");
STATISTIC(numMemcpy, "Number of memcpy operations.");
STATISTIC(numPACMemcpy, "Number of memcpy operations protected with DVI-PAC.");
STATISTIC(numAllocFree, "Number of malloc and free operations.");
STATISTIC(numPACAllocFree, "Number of malloc and free operations protected with DVI-PAC.");
STATISTIC(numInitStores, "Number of initialization memory stores.");
STATISTIC(numPACInitStores, "Number of initialization memory stores protected with DVI-PAC.");

// Initialize DVI-PAC functions so that they don't get eliminated.
bool initDVIPAC = false;

namespace {
	class InitDVIPACPass : public ModulePass {
	public:
		static char ID;
		InitDVIPACPass() : ModulePass(ID) {
			initializeInitDVIPACPassPass(*PassRegistry::getPassRegistry());
		}
		~InitDVIPACPass() { }

		bool doInitialization(Module &M) override {
			outs() << "InitDVIPACPass initializtion\n";
			return false;
		}
/*
		void getAnalysisUsage(AnalysisUsage &AU) const override {
			AU.addRequired<TargetLibraryInfoWrapperPass>();
		}
*/
		// Print stats
		static void printStat(raw_ostream &OS, Statistic &S){
			OS << format("%8u %s - %s\n", S.getValue(), S.getName(), S.getDesc());
		}

		// Insert Set Meta Library call. This is because setMetadata takes three arguements.
        void insertSetMetaLibCall(Value* ArgVal, Instruction* InsertPointInst, StringRef FunctionName, unsigned int Elements, int typeSize){
            LLVMContext &C = InsertPointInst->getFunction()->getContext();
            Value* NumElements = ConstantInt::get(Type::getInt64Ty(C), Elements);
            Value* TypeSize = ConstantInt::get(Type::getInt64Ty(C), typeSize);
            IRBuilder<> builder(C);

            Type* Ty = Type::getInt8Ty(C)->getPointerTo();
            // Insertion point after passed instruction
            builder.SetInsertPoint(InsertPointInst->getNextNode());

            ArrayRef<Type*> FuncParams = {
                Ty->getPointerTo(),
                NumElements->getType(),
                TypeSize->getType()
            };

            Type* ResultFTy = Type::getVoidTy(C);
            FunctionType* FTy = FunctionType::get(ResultFTy, FuncParams, false);

            FunctionCallee Func = InsertPointInst->getModule()->getOrInsertFunction(FunctionName, FTy);
            ArrayRef<Value*> FuncArgs = {
                builder.CreatePointerCast(ArgVal, Ty->getPointerTo()),
                NumElements,
                TypeSize
            };

            builder.CreateCall(Func, FuncArgs);
        }

        // Insert Library call.
        CallInst* insertLibCallAfter(Value* ArgVal, Instruction* InsertPointInst, StringRef FunctionName){
            LLVMContext &C = InsertPointInst->getFunction()->getContext();
            IRBuilder<> builder(C);

            Type* Ty = Type::getInt8Ty(C)->getPointerTo();
            // Insertion point after passed instruction
            builder.SetInsertPoint(InsertPointInst->getNextNode());

            ArrayRef<Type*> FuncParams = {
                Ty->getPointerTo()
            };

            Type* ResultFTy = Type::getVoidTy(C);
            FunctionType* FTy = FunctionType::get(ResultFTy, FuncParams, false);

            FunctionCallee Func = InsertPointInst->getModule()->getOrInsertFunction(FunctionName, FTy);
            ArrayRef<Value*> FuncArgs = {
                builder.CreatePointerCast(ArgVal, Ty->getPointerTo())
            };

            return builder.CreateCall(Func, FuncArgs);
        }

		//Instrument initializers for library functions. This is necessary so that they don't get optimized out by LTO.
		void instrumentInit (Module &M){
			LLVMContext &C = M.getContext();
			Function* FInit = Function::Create(FunctionType::get(Type::getVoidTy(C), false), GlobalValue::InternalLinkage, "initInstrument", &M);
			BasicBlock* Entry = BasicBlock::Create(C, "entry", FInit);
			IRBuilder<> builder(C);
			builder.SetInsertPoint(Entry);
			builder.CreateRetVoid();

			for (auto &F : M) {
				// Skip LLVM functions.
				if (isLLVMFunction(F.getName()) && !F.isDeclaration()){
					continue;
				}

				for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
					BasicBlock *BB = &*FIt;
					for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
						Instruction *I = &*BBIt;
						for (auto GIt = M.global_begin(); GIt != M.global_end(); ++GIt){
							GlobalVariable* GV = dyn_cast<GlobalVariable>(&*GIt);
							Type* Ty = GV->getType();
//							if (!Ty->isPointerTy()){
//								continue;
//							}
							//Ty->dump();
                    	    DataLayout DL = DataLayout(I->getModule());
                        	int typeSize = DL.getTypeAllocSize(Ty);
	
							if (!initDVIPAC){
								outs() << "####INITIALIZATION####\n";
								builder.SetInsertPoint(builder.GetInsertBlock()->getTerminator());

								Value* NumElements = ConstantInt::get(Type::getInt64Ty(C), 1);
								Value* TypeSize = ConstantInt::get(Type::getInt64Ty(C), typeSize);
								ArrayRef<Type*> FuncParams = {
									Ty->getPointerTo(),
									NumElements->getType(),
									TypeSize->getType()
								};
	
								ArrayRef<Type*> FuncParams1 = {
									Ty->getPointerTo(),
								};

								Type* ResultFTy = Type::getVoidTy(C);
								
								FunctionType* FTy = FunctionType::get(ResultFTy, FuncParams, false);
								FunctionCallee Func = M.getOrInsertFunction(SETMETA1, FTy);
								ArrayRef<Value*> FuncArgs = {
									builder.CreatePointerCast(GV, Ty->getPointerTo()),
									NumElements,
									TypeSize
								};

								outs() << "InitSetMeta\n";

								FunctionType* FTy1 = FunctionType::get(ResultFTy, FuncParams, false);
								FunctionCallee Func1 = M.getOrInsertFunction(SETMETAOBJ1, FTy1);
								ArrayRef<Value*> FuncArgs1 = {
									builder.CreatePointerCast(GV, Ty->getPointerTo()),
									NumElements,
									TypeSize
								};

								outs() << "InitSetMetaObj\n";
													
								FunctionType* FTy2 = FunctionType::get(ResultFTy, FuncParams1, false);
								FunctionCallee Func2 = M.getOrInsertFunction(ADDPAC1, FTy2);
								ArrayRef<Value*> FuncArgs2 = {
                    	             builder.CreatePointerCast(GV, Ty->getPointerTo()),
                        	    };

								outs() << "InitAddPAC\n";
	
								FunctionType* FTy3 = FunctionType::get(ResultFTy, FuncParams1, false);
								FunctionCallee Func3 = M.getOrInsertFunction(AUTHPAC1, FTy3);
								ArrayRef<Value*> FuncArgs3 = {
	                                 builder.CreatePointerCast(GV, Ty->getPointerTo()),
    	                        };

								outs() << "InitAuthPAC\n";

								FunctionType* FTy4 = FunctionType::get(ResultFTy, FuncParams1, false);
								FunctionCallee Func4 = M.getOrInsertFunction(REMOVEMETA1, FTy4);
								ArrayRef<Value*> FuncArgs4 = {
            	                     builder.CreatePointerCast(GV, Ty->getPointerTo()),
	                            };

								outs() << "InitRemoveMeta\n";
	
								FunctionType* FTy5 = FunctionType::get(ResultFTy, FuncParams1, false);
								FunctionCallee Func5 = M.getOrInsertFunction(REMOVEMETASTACK1, FTy5);
								ArrayRef<Value*> FuncArgs5 = {
                    	             builder.CreatePointerCast(GV, Ty->getPointerTo()),
                        	    };										

								outs() << "InitRemoveMetaStack\n";
	
								builder.CreateCall(Func, FuncArgs);
								builder.CreateCall(Func1, FuncArgs1);
								builder.CreateCall(Func2, FuncArgs2);
								builder.CreateCall(Func3, FuncArgs3);
								builder.CreateCall(Func4, FuncArgs4);
								builder.CreateCall(Func5, FuncArgs5);

								appendToGlobalCtors(M, FInit, 0);
								initDVIPAC = true;
								outs() << "####INITIALIZATION####\n";	
							}
						}
					}		
				}
			}
		}

		//2nd attempt - Instrument initializers for library functions. This is necessary so that they don't get optimized out by LTO.
        void instrumentInit2(Module &M){
            outs() << "Initialization - 2nd attempt\n";
            for (auto &F : M){
                for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
                    BasicBlock *BB = &*FIt;
                    for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
                        Instruction *I = &*BBIt;
                        if (StoreInst *SI = dyn_cast<StoreInst>(I)){
							if (!initDVIPAC){
								outs() << "Init store\n"; 
								insertLibCallAfter(SI->getPointerOperand(), I, REMOVEMETA1);
								insertLibCallAfter(SI->getPointerOperand(), I, REMOVEMETASTACK1);
								insertLibCallAfter(SI->getPointerOperand(), I, AUTHPAC1);
								insertLibCallAfter(SI->getPointerOperand(), I, ADDPAC1);
								insertSetMetaLibCall(SI->getPointerOperand(), I, SETMETA1, 1, 8);
								insertSetMetaLibCall(SI->getPointerOperand(), I, SETMETAOBJ1, 1, 8);
								initDVIPAC = true;
							}
						}
					}
				}
			}
		}
				
		bool runOnModule (Module &M) override {
			outs() << "InitDVIPACPass module \n";

//			M.dump();

			//Instrumentation initialization
//			instrumentInit(M);
//			instrumentInit2(M);
//			M.dump();
			
			// DEBUG: Printing of values to confirm their correctness

/*			
			outs() << "Init DVI-PAC Statistics\n";
			printStat(outs(), addPAC_count);
			printStat(outs(), authPAC_count);
			printStat(outs(), setMeta_count);
			printStat(outs(), removeMeta_count);
			printStat(outs(), numStores);
			printStat(outs(), numPACStores);
			printStat(outs(), numLoads);
			printStat(outs(), numPACLoads);
			printStat(outs(), numMemcpy);
			printStat(outs(), numPACMemcpy);
			printStat(outs(), numAllocFree);
			printStat(outs(), numPACAllocFree);
			printStat(outs(), numInitStores);
			printStat(outs(), numPACInitStores);
*/
			return true;
		}

		bool isLLVMFunction(StringRef s){
			return s.startswith("llvm.") || s.startswith("__llvm__");
		}
	};
}

char InitDVIPACPass::ID = 0;
INITIALIZE_PASS(InitDVIPACPass, // Name of pass class, e.g., MyAnalysis
        "init-dvi-pac", // Command-line argument to invoke pass
        "Init DVI PAC implementation", // Short description of pass
        false, // Does this pass modify the control-flow graph?
        false) // Is this an analysis pass?

namespace llvm {
    ModulePass *createInitDVIPACPass() {
        return new InitDVIPACPass();
    }
}

