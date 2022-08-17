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
StringRef INITMEMORY("init_memory");
StringRef ADDPAC("addPAC");
StringRef AUTHPAC("authenticatePAC");
StringRef ADDPACNULL("addPACNull");
StringRef AUTHPACNULL("authenticatePACNull");
StringRef SETMETA("setMetadata");
StringRef SETMETAOBJ("setMetadataObj");
StringRef REMOVEMETA("removeMetadata");
StringRef REMOVEMETASTACK("removeMetadataStack");
StringRef METAEXISTS("metadataExists");
StringRef REPLACESIGN("replaceWithSignedPointer");


// Statistics regarding instructions and to count number of times each function is instrumented.
#define DEBUG_TYPE "DVIPACPass"
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
STATISTIC(numReplace_count, "Number of replaceWithSignedPAC functions");

// Data structures
// A list of all values that require metadata to be stored.
struct elementData{
	unsigned int numElements;
	int typeSize;
	StringRef function;
};

unordered_map<Value*, elementData> SetMetaValues;

// Map to store visited structs to prevent infinite recursion
typedef DenseMap<PointerIntPair<Type*, 1>, bool> TypesProtectInfoTy;
TypesProtectInfoTy StructTypeProtectInfo;

// A list of all legitimate indirect functions used by the program. These require metadata to be stored.
unordered_map<Value*, StringRef> SetMetaIndValues;

// A list of all values to be instrumented with CPS mechanism.
SetVector<Value*> CPSValues;
bool isCPS = false;

// A list of all values that require a PAC to be added to the pointer.
SetVector<Value*> AddPACValues;

// A list of all values that require a PAC to be authenticated.
SetVector<Value*> AuthPACValues;

// A list of all values that require a PAC to be re-added to the pointer after authentication. This is a temporary solution, at least for function pointers until we add BLRAA.
SetVector<Value*> AddPACDerefValues;

// A list of all values that need to have removeMetadata instrumented before them. These are mainly deallocations (free, 
// munmap) and return addresses.
SetVector<Value*> removeMetaValues;

// Globals instrumented
bool globalsInstrumented = false;

// Init Memory
bool hashtableInitialized = false;

// Use the replace instead of addpac
bool isReplace = false;

namespace {
	class DVIPACPass : public ModulePass {
	public:
		static char ID;
		DVIPACPass() : ModulePass(ID) {
			initializeDVIPACPassPass(*PassRegistry::getPassRegistry());
		}
		~DVIPACPass() { }

		bool doInitialization(Module &M) override {
			return false;
		}

		void getAnalysisUsage(AnalysisUsage &AU) const override {
			AU.addRequired<TargetLibraryInfoWrapperPass>();
		}

		// Function to check and populate SetMetaIndValues with legitimate indirect functions used.
		void checkIndFunction(Module &M){
			for (auto &F : M){
				for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
					BasicBlock *BB = &*FIt;
					for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
						Instruction *I = &*BBIt;
						int i = 0;
						if (StoreInst *SI = dyn_cast<StoreInst>(I)){
							Value* V = SI->getValueOperand();
							Type* VTy = V->getType();
							if(VTy->isPointerTy() && cast<PointerType>(VTy)->getElementType()->isFunctionTy()){
								SetMetaIndValues[I] = F.getName();
							}

							for (auto SetMIt = SetMetaIndValues.begin(); SetMIt != SetMetaIndValues.end(); ++SetMIt){
								StoreInst* SI = dyn_cast<StoreInst>(SetMIt->first);
								Value* VI = SI->getValueOperand();
								if (V == VI){
									++i;
									if (i == 2){
										SetMetaIndValues.erase(I);
										i = 0;
										break;
									}
								}
							}
						}
					}
				}
			}
		}

		// Function to check the function for sensitive pointers.
		void checkFunction(Function &F){
#ifdef CPS
			isCPS = true;
#endif
			const TargetLibraryInfo *TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					if (isa<PHINode>(I) || isa<LandingPadInst>(I)){
						continue;
					}

					AllocaInst *AI = dyn_cast<AllocaInst>(I);
					if (AI){
						Type *Ty = AI->getAllocatedType(); 
						Value* VA = &*AI;
						// Get type size.
						DataLayout DL = DataLayout(AI->getModule());
						int typeSize = DL.getTypeAllocSize(Ty);

						if (shouldProtectType(Ty)  && !isCPS){
							if (ArrayType *ATy = dyn_cast<ArrayType>(Ty)){
								unsigned int numElements = ATy->getNumElements();
								for (unsigned int i = 0; i < numElements; i++){
									Value* V = insertGEP(I->getNextNode(), i, ATy, VA);
									SetMetaValues[V] = {numElements, typeSize, F.getName()};
								}
							}

							else if (StructType *STy = dyn_cast<StructType>(Ty)){
								SetMetaValues[I] = {1, typeSize, F.getName()};
								insertStructMemberGEP(I->getNextNode(), STy, VA, typeSize);
							}

							else{
								SetMetaValues[I] = {1, typeSize, F.getName()};
							}
						}

						else if (isCPS && shouldProtectTypeFP(Ty)){
							SetMetaValues[I] = {1, typeSize, F.getName()};
						}
					}

					else if (CallInst *CI = dyn_cast<CallInst>(I)){
						Function *CF = CI->getCalledFunction();

						if (CF && isLLVMFunction(CF->getName())){
							continue;
						}

						if(CF){
						}

						if (CI->isTailCall()){
							continue;
						}
					
						if(CF && !CI->arg_empty()){
							Value* VArg = CI->getArgOperand(0);
							if(shouldProtectType(VArg->getType())){
								if(GetElementPtrInst* GEPArg = dyn_cast<GetElementPtrInst>(VArg)){
									AuthPACValues.insert(I);
								}
							}
						}

						
						// Here we look for the store instruction after the allocation, 
						// and check if the pointer is sensitive. If it is, we add it to our setMeta set 
						// (setMetadata for the allocated object). We also remove the value that was set on 
						// the alloca (stack).
						if (CF && isAllocationFn(CI, TLI, true)){
							++numAllocFree;
							Instruction* nextStoreInst = checkStoreInstructionForMalloc(CI);
							if(isa<StoreInst>(nextStoreInst)){
								Value* V = cast<StoreInst>(nextStoreInst)->getPointerOperand();
								PointerType* PTy;
								if(BitCastInst* BCI = dyn_cast<BitCastInst>(CI->getNextNode())){
									PTy = cast<PointerType>(BCI->getDestTy());
								}
								else{
									PTy = cast<PointerType>(CI->getFunctionType()->getReturnType());
								}

								Type* VTy = V->getType();
								StoreInst* SI = cast<StoreInst>(nextStoreInst);
								Value* VSI = SI->getValueOperand();

								if(ConstantExpr* CE = dyn_cast<ConstantExpr>(SI->getValueOperand())){
				                                    	Value* VCE = CE->getOperand(0);
                                					if(BitCastInst* BI = dyn_cast<BitCastInst>(VCE)){
					                                        Value* VB = BI->getOperand(0);
										if(GlobalValue* GV = dyn_cast<GlobalValue>(VB)){
											if(GV->getSection().startswith("llvm")){
												continue;
											}
										}
									}
								}

								if(shouldProtectType(VTy)){
									++numPACAllocFree;
									for (auto SVIt = SetMetaValues.begin(); SVIt != SetMetaValues.end(); ++SVIt){
										Value* SVV = SVIt->first;
										if (V == SVV){
											SetMetaValues.erase(V);
											break;
										}
									}
									// Get type size.
									DataLayout DL = DataLayout(nextStoreInst->getModule());
									int typeSize = DL.getTypeAllocSize(PTy->getElementType());
								
									// Allocated size by malloc, calloc, mmap.
									unsigned allocSize = 8;
									if (isMallocLikeFn(CI, TLI, true)){
										allocSize = getIntValue(CI->getArgOperand(0));
									}
									else if(isMmapFunction(CF->getName())){
										allocSize = getIntValue(CI->getArgOperand(1));
									}
									else if(isCallocLikeFn(CI, TLI, true)){
										unsigned countSize = getIntValue(CI->getArgOperand(0));
										unsigned objSize = getIntValue(CI->getArgOperand(1));
										allocSize = countSize * objSize;
									}
									else if(isReallocLikeFn(CI, TLI, true)){
										allocSize = getIntValue(CI->getArgOperand(1));
									}

									// Number of elements
									unsigned int numElements = allocSize/typeSize;
								
									if (!isCPS && numElements == 1){
										SetMetaValues[nextStoreInst] = {1, typeSize, F.getName()};
									}
									else if (!isCPS && !isI8Pointer(V)){
										Value* VL = insertLoad(nextStoreInst, V);
										for (unsigned int i = 0; i < numElements; i++){
											Value* VA = insertArrayGEP(nextStoreInst->getNextNode(), i, VSI->getType()->getPointerElementType(), VL);
											SetMetaValues[VA] = {numElements, typeSize, F.getName()};										
										}
									}
									else if (isCPS && shouldProtectTypeFP(VTy) && numElements == 1 ){
										SetMetaValues[nextStoreInst] = {1, typeSize, F.getName()};
									}
								}
							}
						}
						// Here we are adding the PAC again after the sensitive function call. Before the 
						// function is called it has to be loaded, and so we check if the previous instruction
						// is a load and if it's PointerOperand is sensitive. We know that the PAC has already
						// been authenticated. 
						else if (CI->isIndirectCall()){						
							if (isCPS){
								CPSValues.insert(I);
							}
							else {
								AddPACDerefValues.insert(I);
							}
						}

						// Handling memcpy
						else if (CF && isMemcpyFunction(CF->getName())){
							++numMemcpy;
							Value* src = CI->getArgOperand(1);
							Value* dest = CI->getArgOperand(0);
							Type* realSrcType = getOperandRealType(src);
							Type* realDestType = getOperandRealType(dest);
							if (shouldProtectType(realSrcType) && !isCPS){
								AuthPACValues.insert(I);
							}

							else if (shouldProtectTypeFP(realSrcType) && isCPS){
								AuthPACValues.insert(I);
							}

							if (shouldProtectType(realDestType) && !isCPS){
								AuthPACValues.insert(I);
							}
							else if (shouldProtectTypeFP(realDestType) && isCPS){
								AuthPACValues.insert(I);
							}
						}

						else if (CF && isDeallocLibFunction(CF->getName())){
							if(BitCastInst* BI = dyn_cast<BitCastInst>(CI->getArgOperand(0))){
								if(LoadInst* LI = dyn_cast<LoadInst>(BI->getOperand(0))){
									if(shouldProtectType(LI->getPointerOperand()->getType())){
										removeMetaValues.insert(I);
									}
								}
							}
							else if(LoadInst* LI = dyn_cast<LoadInst>(CI->getArgOperand(0))){
								if(shouldProtectType(LI->getPointerOperand()->getType())){
									removeMetaValues.insert(I);
								}
							}
						}

						else if(ConstantExpr* CE = dyn_cast<ConstantExpr>(CI->getCalledOperand())){
							if(Function* CF = dyn_cast<Function>(CE->getOperand(0))){
								if(isDeallocLibFunction(CF->getName())){
									if(BitCastInst* BI = dyn_cast<BitCastInst>(CI->getArgOperand(0))){
										if(LoadInst* LI = dyn_cast<LoadInst>(BI->getOperand(0))){
											if(shouldProtectType(LI->getPointerOperand()->getType())){
												removeMetaValues.insert(I);
											}
										}
									}
									else if(LoadInst* LI = dyn_cast<LoadInst>(CI->getArgOperand(0))){
										if(shouldProtectType(LI->getPointerOperand()->getType())){
											removeMetaValues.insert(I);
										}
									}
								}
							}
						}
					
						else if (CF){
							++numAllocFree;
							Instruction* nextStoreInst = checkStoreInstructionForMalloc(CI);
							if(isa<StoreInst>(nextStoreInst)){
								Value* V = cast<StoreInst>(nextStoreInst)->getPointerOperand();
								StoreInst* SI = cast<StoreInst>(nextStoreInst);
								if(ConstantExpr* CE = dyn_cast<ConstantExpr>(SI->getValueOperand())){
									Value* VCE = CE->getOperand(0);
									if(BitCastInst* BI = dyn_cast<BitCastInst>(VCE)){
										Value* VB = BI->getOperand(0);
										if(GlobalValue* GV = dyn_cast<GlobalValue>(VB)){
											if(GV->getSection().startswith("llvm")){
												continue;
                                            						}
                                        					}
                                    					}
                                				}
								Type* VTy = V->getType();
								if(shouldProtectType(VTy)){
									++numPACAllocFree;
									for (auto SVIt = SetMetaValues.begin(); SVIt != SetMetaValues.end(); ++SVIt){
										Value* SVV = SVIt->first;
										if (V == SVV){
											SetMetaValues.erase(V);
											break;
										}
									}
									// Get type size.
									DataLayout DL = DataLayout(nextStoreInst->getModule());
									int typeSize = DL.getTypeAllocSize(VTy);
								
									if (!isCPS){
										SetMetaValues[nextStoreInst] = {1, typeSize, F.getName()};
									}
									
									else if (isCPS && shouldProtectTypeFP(VTy)){
										SetMetaValues[nextStoreInst] = {1, typeSize, F.getName()};
									}
								}
							}
						}
						
					}

					else if (StoreInst *SI = dyn_cast<StoreInst>(I)){
						++numStores;
						if(GlobalValue* GV = dyn_cast<GlobalValue>(SI->getPointerOperand())){
                            				if(GV->getName().startswith("__") || GV->getSection().startswith("llvm")){
                                				continue;
                            				}
							continue;
                        			}

						if(GlobalValue* GVV = dyn_cast<GlobalValue>(SI->getValueOperand())){
                            				if(GVV->getName().startswith("__") || GVV->getSection().startswith("llvm")){
                                				continue;
                            				}
                        			}

						
						Type* Ty = SI->getPointerOperand()->getType();
						if(isCPS){
							Value* VSI = SI->getValueOperand();
							Type* VTy = SI->getValueOperand()->getType();

							// Function pointer
							if (VTy->isPointerTy() && cast<PointerType>(VTy)->getElementType()->isFunctionTy()){
								++numPACStores;
								CPSValues.insert(I);
							}

							if(BitCastInst* BSI = dyn_cast<BitCastInst>(VSI)){		
								Value* BO = BSI->getOperand(0);
								PointerType* PTy = cast<PointerType>(BSI->getDestTy());
								if(CallInst* CSI = dyn_cast<CallInst>(BO)){
									if(isMallocLikeFn(CSI, TLI, true)){
										DataLayout DL = DataLayout(SI->getModule());
										int typeSize = DL.getTypeAllocSize(PTy->getElementType());
										unsigned allocSize = getIntValue(CSI->getArgOperand(0));
										unsigned int numElements = allocSize/typeSize;
										if(numElements == 1 && shouldProtectTypeFP(BSI->getDestTy())){
											CPSValues.insert(I);
										}
									}
								}
							}
						}
						
						Value* VRHS = SI->getValueOperand();
						if(VRHS->getName() == "incdec.ptr" || VRHS->getName().startswith("__")){
							continue;
						}

						if (shouldProtectType(Ty)  && !isCPS){
							++numPACStores;
							AddPACValues.insert(I);
						}
						GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(SI->getPointerOperand());
						if(GEPI && !isCPS){
							Value* GEPV = GEPI->getPointerOperand();
							Type* GEPTy = GEPV->getType();
							if(shouldProtectType(GEPTy)){
								if(LoadInst* GEPLI = dyn_cast<LoadInst>(GEPV)){
									AddPACValues.insert(GEPLI);
								}
							}
						}
					}

					else if (LoadInst *LI = dyn_cast<LoadInst>(I)){
						++numLoads;
						Type* Ty = LI->getPointerOperand()->getType();
						Value* V = LI->getPointerOperand();
						bool noInstrument = false;

						if(GlobalValue* GV = dyn_cast<GlobalValue>(LI->getPointerOperand())){
							if(GV->getName().startswith("__") || GV->getSection().startswith("llvm")){
								continue;
							}
						}

						//CPS
						// Function pointer
						if(isCPS && !noInstrument){
							if(AllocaInst* AI = dyn_cast<AllocaInst>(V)){
								for (auto SetMIt = SetMetaValues.begin(); SetMIt != SetMetaValues.end(); ++SetMIt){
									if(StoreInst* SI = dyn_cast<StoreInst>(SetMIt->first)){
										if(AllocaInst* ASI = dyn_cast<AllocaInst>(SI->getPointerOperand())){
											if(ASI == AI){
												Type* ATy = AI->getAllocatedType();
												if (shouldProtectTypeFP(ATy)){
													if(StoreInst *SI = dyn_cast<StoreInst>(I->getNextNode())){
														if(LI == SI->getValueOperand()){
															continue;
														}
													}
													if(isa<GetElementPtrInst>(I->getNextNode())){
														continue;
													}
													CPSValues.insert(I);
												}
											}
										}
									}
									else if(AllocaInst* ASI = dyn_cast<AllocaInst>(SetMIt->first)){
										if(ASI == AI){
											Type* ATy = AI->getAllocatedType();
											if (shouldProtectTypeFP(ATy)){
												if(StoreInst *SI = dyn_cast<StoreInst>(I->getNextNode())){
													if(LI == SI->getValueOperand()){
														continue;
													}
												}
												if(isa<GetElementPtrInst>(I->getNextNode())){
													continue;
												}
							
												CPSValues.insert(I);
											}
										}
									}
								}
							}
							else if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(V)){
								Type* GTy = GEPI->getResultElementType();
								if (GTy->isPointerTy() && cast<PointerType>(GTy)->getElementType()->isFunctionTy()){
									CPSValues.insert(I);
								}
							}
							else if (shouldProtectTypeFP(LI->getType())){
									CPSValues.insert(I);
							}
						}

						else if ((shouldProtectType(Ty) && !noInstrument && LI->getName() != "gep_load") || (isBitcastIntoSensitive(LI) && !noInstrument && LI->getName() != "gep_load")){
							++numPACLoads;
							if (V == LI->getPrevNonDebugInstruction()){
								if(LoadInst* LII = dyn_cast<LoadInst>(LI->getPrevNonDebugInstruction())){
									if (LI->getPointerOperandType() == LII->getType()){
										AuthPACValues.insert(I);
									}
									else{
										continue;
									}
								}
							}

							if(V->getName() == "incdec.ptr" || V->getName().startswith("__")){
								continue;
							}


							if(LI->getName().startswith("vtable")){
								continue;
							}

							if(V->getName().startswith("vfn")){
								continue;
							}
							AuthPACValues.insert(I);
						}
					}

					else if (BitCastInst* BI = dyn_cast<BitCastInst>(I)){
						Type* SrcTy = BI->getSrcTy();
						Type* DestTy = BI->getDestTy();
						Value* VBI = BI->getOperand(0);
						if(shouldProtectType(SrcTy) && !shouldProtectType(DestTy)){
							if(LoadInst* LBI = dyn_cast<LoadInst>(VBI)){
								if(isa<AllocaInst>(LBI->getPointerOperand()) || isa<GlobalValue>(LBI->getPointerOperand())){
									continue;
								}
							}
							if(isa<CallInst>(VBI)){
								if(isa<StructType>(isStruct(SrcTy))){
									AuthPACValues.insert(BI);
								}	
							}
						}
					}
				}
			}
		}
		
		// Finds the store instruction associated with the malloc call.
		Instruction* checkStoreInstructionForMalloc(Instruction* I){
			if (isa<ReturnInst>(I) || I->isTerminator()){
				return I;
			}
			Instruction* nextStoreInst = I->getNextNode();
			if (isa<StoreInst>(nextStoreInst)){
				return nextStoreInst;
			}
			else {
				return checkStoreInstructionForMalloc(nextStoreInst);
			}
			return nextStoreInst;
		}

		// Finds the last GEP instruction that sets the metadata. This is necessary
		// to allow addPAC to be instrumented after the new instructions are added.
		Instruction* checkEndOFGEP(Instruction* I){
			Instruction* nextGEP = I->getNextNode();
			if (isa<GetElementPtrInst>(nextGEP)){
				return checkEndOFGEP(nextGEP);
			}
			else {
				return nextGEP;
			}
			return nextGEP;
		}

		// Finds if there are any stores for the operand of the instruction. This is necessary
		// to allow addPAC to be instrumented after the load if there are no stores.
		int checkIfStore(Instruction* I, LoadInst* LI){
			int i = 0;
			if (isa<ReturnInst>(I) || I->isTerminator()){
				return 0;
			}

			else if (StoreInst* SI = dyn_cast<StoreInst>(I)){
				Value* VI = dyn_cast<Value>(LI);
				Value* VSI = SI->getPointerOperand();
				Value* VLI = SI->getValueOperand();
				if(VI == VLI){
					return 1;
				}
				else if (VI == VSI){
					return 0;
				}
				else {
					i = checkIfStore(I->getNextNode(), LI);
				}
			}

			else {
				i = checkIfStore(I->getNextNode(), LI);
			}
			return i;
		}

		// Finds the immediate GEP instruction. This is necessary for RHS loads
		// to allow addPAC to be instrumented after the new instructions are added.
		Instruction* checkLastGEP(Instruction* I){	
			if (isa<ReturnInst>(I) || I->isTerminator()){
				return I;
			}
			Instruction* nextGEP = I->getNextNode();
			if (isa<GetElementPtrInst>(nextGEP)){
				return nextGEP;
			}

			else {
				return checkLastGEP(nextGEP);
			}

			return nextGEP;
		}

		// Finds the last Load instruction that sets the metadata. This is necesarry
		// to allow addPAC to be instrumented after the new instructions are added.
		Instruction* checkEndOFLoad(Instruction* I){
			if(Instruction* nextLoad = dyn_cast<LoadInst>(I->getNextNode())){
				if (isa<LoadInst>(nextLoad)){
					return checkEndOFLoad(nextLoad);
				}
				else {
					return nextLoad;
				}
			}
			return I;
		}

		Value* insertGEP (Instruction *insertPoint, int index, Type* Ty, Value *V) {
			LLVMContext &C = insertPoint->getFunction()->getContext();
			IRBuilder<> IRB(C);
			IRB.SetInsertPoint(insertPoint);
			vector<Value*> indices(2);
			indices[0] = ConstantInt::get(C, llvm::APInt(32, 0, true));
			indices[1] = ConstantInt::get(C, APInt(32, index, true));
			return IRB.CreateInBoundsGEP(Ty, V, indices, "memberptr");
		}
	
		Value* insertArrayGEP(Instruction* insertPoint, unsigned int index, Type* Ty, Value* V){
			LLVMContext& C = insertPoint->getFunction()->getContext();
			IRBuilder<> IRB(C);
			IRB.SetInsertPoint(insertPoint->getNextNode());
			Value* indexVal = ConstantInt::get(C,APInt(64, index, true));
			return IRB.CreateInBoundsGEP(Ty, V, indexVal, "arrayidx");
		}

		Value* insertBitCast(Instruction* insertPoint, Type* destTy, Value* V){
			LLVMContext& C = insertPoint->getFunction()->getContext();
			IRBuilder<> IRB(C);
			IRB.SetInsertPoint(insertPoint);
			return IRB.CreateBitCast(V, destTy);
		}

		Value* insertLoad(Instruction* insertPoint, Value* V){
			LLVMContext& C = insertPoint->getFunction()->getContext();
			IRBuilder<> IRB(C);
			IRB.SetInsertPoint(insertPoint->getNextNode());
			return IRB.CreateLoad(V, "gep_load");
		}
		
		void insertStructMemberGEP(Instruction* insertPoint, StructType* STy, Value* V, int typeSize){
			if(insertPoint == nullptr){
				return;
			}
			unsigned numElements = STy->getNumElements();
			for (unsigned i = 0; i < numElements; i++){
				if (StructType* ASTy = dyn_cast<StructType>(STy->getElementType(i))){
					Value* VS = insertGEP(insertPoint, i, STy, V);
					SetMetaValues[VS] = {1, typeSize, "struct_member"};					
					insertStructMemberGEP(insertPoint->getNextNode(), ASTy, VS, typeSize);
				}
			}
		}

		void insertGlobalStructMemberGEP(Instruction* insertPoint, StructType* STy, Value* V, int typeSize){
			unsigned numElements = STy->getNumElements();
			for (unsigned i = 0; i < numElements; i++){
				if (StructType* ASTy = dyn_cast<StructType>(STy->getElementType(i))){
					Value* VS = insertGEP(insertPoint, i, STy, V);
					insertSetMetaLibCall(VS, insertPoint, SETMETA, 1, typeSize);
					insertGlobalStructMemberGEP(insertPoint->getNextNode(), ASTy, VS, typeSize);
				}
			}
		}


		void recursiveStructInsertions(Value* VS, Value* VGEP, Instruction* I, StringRef StLibCall){
			if (LoadInst *GLI = dyn_cast<LoadInst>(VGEP)){
				Value* VGLI = GLI->getPointerOperand();
				CallInst* CL = insertLibCallAfter(VGLI, I, StLibCall);
				++addPAC_count;
				
				if (GetElementPtrInst* VGI = dyn_cast<GetElementPtrInst>(VGLI)){
					recursiveStructInsertions(VGI, VGI->getPointerOperand(), cast<Instruction>(CL), StLibCall);
				}
			}

			else if (GetElementPtrInst *GGI = dyn_cast<GetElementPtrInst>(VGEP)){
				recursiveStructInsertions(GGI, GGI->getPointerOperand(), I, StLibCall);
			}

			else if (BitCastInst *BI = dyn_cast<BitCastInst>(VGEP)){
				if(shouldProtectType(BI->getSrcTy())){
					if (LoadInst *GLI = dyn_cast<LoadInst>(BI->getOperand(0))){
						Value* VGLI = GLI->getPointerOperand();
						CallInst* CL = insertLibCallAfter(VGLI, I, StLibCall);
						++addPAC_count;
						if (GetElementPtrInst* VGI = dyn_cast<GetElementPtrInst>(VGLI)){
							recursiveStructInsertions(VGI, VGI->getPointerOperand(), cast<Instruction>(CL), StLibCall);
						}
					}

					else if (GetElementPtrInst *GGI = dyn_cast<GetElementPtrInst>(VGEP)){
						recursiveStructInsertions(GGI, GGI->getPointerOperand(), I, StLibCall);
					}
				}
			}
		}

		// Check to find if struct is sensitive, in case a non-sensitive store is used. This is necessary
		// to addPAC to sensitive structs when they use non-sensitive members.
		bool isSensitiveStruct(Value* VGEP){
			if (GetElementPtrInst* GI = dyn_cast<GetElementPtrInst>(VGEP)){
				if (LoadInst* LI = dyn_cast<LoadInst>(GI->getPointerOperand())){
					if (shouldProtectType(LI->getPointerOperand()->getType())){
						return true;
					}

					else if (GetElementPtrInst* GLI = dyn_cast<GetElementPtrInst>(LI->getPointerOperand())){
						return isSensitiveStruct(GLI);
					}
				}
			}
			return false;
		}

		Type* isStruct(Type* Ty){
			if (StructType* STy = dyn_cast<StructType>(Ty)){
				return STy;
			}

			else if (PointerType* PTy = dyn_cast<PointerType>(Ty)){
				Type* ETy = PTy->getElementType();
				return isStruct(ETy);
			}

			return Ty;
		}

		Value* authenticateStructMembers(Instruction* insertPoint, StructType* STy, Value* V){
			unsigned numElements = STy->getNumElements();
			LLVMContext &C = insertPoint->getFunction()->getContext();
			IRBuilder<> IRB(C);
			IRB.SetInsertPoint(insertPoint);
			AllocaInst* alloc = IRB.CreateAlloca(STy, 0, "alloca_tmp");
			LoadInst* load = IRB.CreateLoad(V, "load_tmp");
			IRB.CreateStore(load, alloc);
			for (unsigned i = 0; i < numElements; i++){
				if (isa<PointerType>(STy->getElementType(i))){
					vector<Value*> indices(2);
					indices[0] = ConstantInt::get(C, llvm::APInt(32, 0, true));
					indices[1] = ConstantInt::get(C, APInt(32, i, true));
					Value* VS = IRB.CreateInBoundsGEP(STy, alloc, indices, "memberptr");
					insertLibCallAuth(VS, insertPoint, AUTHPAC, 0);
				}
			}
			return cast<Value>(alloc);
		}


		unsigned getIntValue(Value *V) {
			ConstantInt *CI = dyn_cast<ConstantInt>(V);
			while (!dyn_cast<ConstantInt>(V)) {
				if (SExtInst *SEI = dyn_cast<SExtInst>(V)){
					V = SEI->getOperand(0);
				} 

				else if (LoadInst *LI = dyn_cast<LoadInst>(V)){
					V = LI->getOperand(0);
				} 

				else{
					outs() << "UNKNOWN INT VALUE\n";
					return 0;
				}
			}
			return CI->getZExtValue();
		}

		// Function to check if the key is present in unordered_map or not 
		bool check_key(unordered_map<Value*, elementData> m, Value* key) { 
			// Key is not present
			if (m.find(key) == m.end()) 
				return false; 
			return true; 
		} 

		// Check for i8* type
		bool isI8Pointer(Value* V){
			if (PointerType *PTy = dyn_cast<PointerType>(V->getType())){
				if (PointerType *PTy1 = dyn_cast<PointerType>(PTy->getPointerElementType())){
					if (IntegerType *ITy = dyn_cast<IntegerType>(PTy1->getPointerElementType())){
						if (ITy->getBitWidth() == 8){
							return true;
						}
					}
				}
			}
			return false;
		}

		// Checks if the value is ever casted later to a sensitive type.
		Type* isBitcastIntoSensitive(Value* V){
			for (const Use &UI : V->uses()){
				auto I = dyn_cast<Instruction>(UI.getUser());
				if (!I){
					continue;
				}

				if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)){
					Type* DTy = BCI->getDestTy();
					if(shouldProtectType(DTy)){
						return DTy;
					}
				}
				else if (StoreInst* SI = dyn_cast<StoreInst>(I)){
					if(SI->getValueOperand()){
						for (const Use &UI : SI->getValueOperand()->uses()){
							auto I = dyn_cast<Instruction>(UI.getUser());
							if(!I){
								continue;
							}
							if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)){
								Type* DTy = BCI->getDestTy(); 
								if(shouldProtectType(DTy)){
									return DTy;
								}
							}
						}
					}
				}
				else if (LoadInst* LI = dyn_cast<LoadInst>(I)){
					if(dyn_cast<Value>(LI)){
						for (const Use &UI : dyn_cast<Value>(LI)->uses()){
							auto I = dyn_cast<Instruction>(UI.getUser());
							if (!I){
								continue;
							}
							if (BitCastInst *BCI = dyn_cast<BitCastInst>(I)){ 
								Type* DTy = BCI->getDestTy();
								if(shouldProtectType(DTy)){
									return DTy;
								}
							}
						}
					}
				}
			}

			return nullptr;
		}


		// Check if type should be protected
		bool shouldProtectType(Type* Ty){
			// Function pointer
			if (Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isFunctionTy()){
				return true;
			}

			// Generic pointer - Recursively find out if it's sensitive
			else if (PointerType* PTy = dyn_cast<PointerType>(Ty)){
				Type* ETy = PTy->getElementType();
				return shouldProtectType(ETy);
			}

			// Array
			else if (ArrayType* ATy = dyn_cast<ArrayType>(Ty)){
				Type* ETy = ATy->getElementType();
				return shouldProtectType(ETy);
			}

			// Struct
			else if (StructType* STy = dyn_cast<StructType>(Ty)){
				if (STy->isOpaque()){
					return false;
				}

				// Fix for infinite struct recursion
				TypesProtectInfoTy::key_type Key(STy, false);
				TypesProtectInfoTy::iterator TIt = StructTypeProtectInfo.find(Key);
				if(TIt != StructTypeProtectInfo.end()){
					return TIt->second;
				}
				StructTypeProtectInfo[Key] = false;

				unsigned numElements = STy->getNumElements();
				for (unsigned i = 0; i < numElements; i++){
					if (shouldProtectType(STy->getElementType(i))){
						StructTypeProtectInfo[Key] = true;
						return true;
					}
				}
			}

			return false;
		}

		// Check if type is FP or drills down to FP
		bool shouldProtectTypeFP(Type* Ty){
			if (Ty->isPointerTy() && cast<PointerType>(Ty)->getElementType()->isFunctionTy()){
				return true;
			}

			// Generic pointer - Recursively find out if it's a FP
			else if (PointerType* PTy = dyn_cast<PointerType>(Ty)){
				Type* ETy = PTy->getElementType();
				return shouldProtectTypeFP(ETy);
			}

			return false;
		}

		int checkIfSensitiveToCall(Value* V){
			int i = 0;
			if(GetElementPtrInst* GI = dyn_cast<GetElementPtrInst>(V)){
				for (const Use &UI : GI->uses()){
					auto VI = cast<Value>(UI.getUser());
					i = checkIfSensitiveToCall(VI);
				}
			}
			else if(LoadInst* LI = dyn_cast<LoadInst>(V)){
				for (const Use &UI : LI->uses()){
					auto VI = cast<Value>(UI.getUser());
					i = checkIfSensitiveToCall(VI);
				}
			}
			else if (isa<CallInst>(V)){
				return 1;
			}

			return i;
		}

		Value* getIfSensitiveToCall(Value* V){
			Value* VC = nullptr;
			if(GetElementPtrInst* GI = dyn_cast<GetElementPtrInst>(V)){
				for (const Use &UI : GI->uses()){
					auto VI = cast<Value>(UI.getUser());
					VC = getIfSensitiveToCall(VI);
				}
			}
			else if(LoadInst* LI = dyn_cast<LoadInst>(V)){
				for (const Use &UI : LI->uses()){
					auto VI = cast<Value>(UI.getUser());
					VC = getIfSensitiveToCall(VI);
				}
			}
			else if (CallInst* CI = dyn_cast<CallInst>(V)){
				VC = cast<Value>(CI);
				return VC;
			}

			return VC;
		}
		
		// Get the real type of operands
		Type* getOperandRealType(Value* V){
			Type* realType = V->getType();
			if(BitCastInst* BCI = dyn_cast<BitCastInst>(V)){
				Value* BCIV = BCI->getOperand(0);
				if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(BCIV)){
					Type* srcType = GEP->getSourceElementType();
					if(isa<StructType>(srcType)){
						realType = GEP->getType();
					}
					else if (isa<ArrayType>(srcType)){
						realType = GEP->getPointerOperandType();
					}
					else {
						realType = srcType;
					}
				}
				else if(LoadInst* LI = dyn_cast<LoadInst>(BCIV)){
					realType = LI->getType();
				}
				else if(AllocaInst* AI = dyn_cast<AllocaInst>(BCIV)){
					realType = AI->getType();
				}
			}
			else if (LoadInst* LI = dyn_cast<LoadInst>(V)){
				realType = LI->getType();
			}
			else {
				realType = V->getType();
			}

			return realType;
		}

		// Get the real type of operands
		Value* getOperandRealValue(Value* V){
			Value* realValue = nullptr;
			if(BitCastInst* BCI = dyn_cast<BitCastInst>(V)){
				Value* BCIV = BCI->getOperand(0);
				if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(BCIV)){
					Type* srcType = GEP->getSourceElementType();
					if(isa<StructType>(srcType)){
						realValue = GEP;
					}
					else if (isa<ArrayType>(srcType)){
						realValue = GEP->getPointerOperand();
					}
					else {
						outs() << "SOURCE TYPE UNKNOWN\n";
					}
				}
				else if(LoadInst* LI = dyn_cast<LoadInst>(BCIV)){
					realValue = LI->getPointerOperand();
				}
				else if(AllocaInst* AI = dyn_cast<AllocaInst>(BCIV)){
					realValue = AI;
				}
			}
			else if (LoadInst* LI = dyn_cast<LoadInst>(V)){
				realValue = LI->getPointerOperand();
			}
			else {
				outs() << "INSTRUCTION UNKNOWN\n";
			}

			return realValue;
		}

		// Insert Set Meta Library call. This is because setMetadata takes three arguements.
		void insertSetMetaLibCall(Value* ArgVal, Instruction* InsertPointInst, StringRef FunctionName, unsigned int Elements, int typeSize){		
			LLVMContext &C = InsertPointInst->getFunction()->getContext();
			Value* NumElements = ConstantInt::get(Type::getInt32Ty(C), Elements);
			Value* TypeSize = ConstantInt::get(Type::getInt32Ty(C), typeSize);
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
			Value* Addr = builder.Insert(CastInst::CreatePointerCast(ArgVal, Ty->getPointerTo(),""));
			ArrayRef<Value*> FuncArgs = {
				Addr,
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

		// Insert Library call.
		CallInst* insertLibCallBefore(Value* ArgVal, Instruction* InsertPointInst, StringRef FunctionName){
			LLVMContext &C = InsertPointInst->getFunction()->getContext();
			IRBuilder<> builder(C);
			
			Type* Ty = Type::getInt8Ty(C)->getPointerTo();
			// Insertion point before passed instruction
			builder.SetInsertPoint(InsertPointInst);

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

		CallInst* insertLibCallAuth(Value* ArgVal, Instruction* InsertPointInst, StringRef FunctionName, unsigned int arrayIndex){
			LLVMContext &C = InsertPointInst->getFunction()->getContext();
			IRBuilder<> builder(C);
			
			Type* Ty = Type::getInt8Ty(C)->getPointerTo();
			Value* ArrayIndex = ConstantInt::get(Type::getInt32Ty(C), arrayIndex);
			// Insertion point before passed instruction
			builder.SetInsertPoint(InsertPointInst);

			ArrayRef<Type*> FuncParams = {
				Ty->getPointerTo(),
				ArrayIndex->getType()
			};

			Type* ResultFTy = Type::getVoidTy(C);
			FunctionType* FTy = FunctionType::get(ResultFTy, FuncParams, false);

			FunctionCallee Func = InsertPointInst->getModule()->getOrInsertFunction(FunctionName, FTy);
			ArrayRef<Value*> FuncArgs = {
				builder.CreatePointerCast(ArgVal, Ty->getPointerTo()),
				ArrayIndex
			};

			return builder.CreateCall(Func, FuncArgs);
		}


		// Print stats
		static void printStat(raw_ostream &OS, Statistic &S){
			OS << format("%8u %s - %s\n", S.getValue(), S.getName(), S.getDesc());
		}


		// Instrument SetMeta values
		void instrumentSetMeta(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto SetMIt = SetMetaValues.begin(); SetMIt != SetMetaValues.end(); ++SetMIt){
						if(I == SetMIt->first){
							if (AllocaInst* AI = dyn_cast<AllocaInst>(SetMIt->first)){
								Value* V = &*AI;
								if (V == I){
									insertSetMetaLibCall(V, I, SETMETA, SetMIt->second.numElements, SetMIt->second.typeSize);
									++setMeta_count;
								}
							}
							else if (StoreInst* SI = dyn_cast<StoreInst>(SetMIt->first)){
								Value* V = SI->getPointerOperand();
								if(StoreInst *SII = dyn_cast<StoreInst>(I)){
									Value* VS = SII->getPointerOperand();
									if(V == VS){
										insertSetMetaLibCall(V, I, SETMETAOBJ, SetMIt->second.numElements, SetMIt->second.typeSize);
										++setMeta_count;
									}
								}
							}

							else if (GetElementPtrInst* GI = dyn_cast<GetElementPtrInst>(SetMIt->first)){
								Type* Ty = GI->getSourceElementType();
								Value* V = &*GI;
								if (isa<ArrayType>(Ty)){
									insertSetMetaLibCall(V, I, SETMETA, SetMIt->second.numElements, SetMIt->second.typeSize);
									++setMeta_count;
								}

								else {
									insertSetMetaLibCall(V, I, SETMETA, SetMIt->second.numElements, SetMIt->second.typeSize);
									++setMeta_count;
								}
							}
						}
					}
				}
			}
		}
		// Add metadata for null pointer
		void instrumentSetMetaNull(Function& F){
			if (F.getName() == "main"){
				Function::iterator FIt = F.begin();
				BasicBlock* BB = &*FIt;
				BasicBlock::iterator BBIt = BB->begin();
				Instruction* I = &*BBIt;
				LLVMContext &C = F.getContext();
				Value* V = llvm::Constant::getNullValue(llvm::Type::getInt8Ty(C)->getPointerTo());
				insertSetMetaLibCall(V, I, SETMETA, 1, 8);
				++setMeta_count;
			}
		}

		// Instrument SetMetaInd values
		void instrumentSetMetaInd(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto SetMIt = SetMetaIndValues.begin(); SetMIt != SetMetaIndValues.end(); ++SetMIt){
						if(I == SetMIt->first){
							if (F.getName()	== SetMIt->second){
								StoreInst* SI = dyn_cast<StoreInst>(SetMIt->first);
								Value* V = SI->getValueOperand();
								// Get type size.
								DataLayout DL = DataLayout(SI->getModule());
								int typeSize = DL.getTypeAllocSize(V->getType());
								insertSetMetaLibCall(V, I, SETMETA, 1, typeSize);
								++setMeta_count;
							}
						}
					}
				}
			}
		}


		// Instrument AddPAC values
		void instrumentAddPAC(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto AddPIt = AddPACValues.begin(); AddPIt != AddPACValues.end(); ++AddPIt){
						if(I == *AddPIt){
							if (LoadInst* LI = dyn_cast<LoadInst>(*AddPIt)){
								Value* V = LI->getPointerOperand();
								if(LoadInst *LII = dyn_cast<LoadInst>(I)){
									Value* VI = LII->getPointerOperand();
									int isCheckIfStore = checkIfStore(I->getNextNode(), LII);
									if (V == VI && !isa<GetElementPtrInst>(I->getNextNode())){
										bool isGEP = false;
										if(GetElementPtrInst* GEPI = dyn_cast<GetElementPtrInst>(checkLastGEP(I))){
											LoadInst* GEPLI = dyn_cast<LoadInst>(GEPI->getPointerOperand());
											if(GEPLI){
												AllocaInst* GEPAI = dyn_cast<AllocaInst>(GEPLI->getPointerOperand());
												if(GEPAI && VI == GEPAI){
													isGEP = true;
												}
											}
										}
										if(isGEP == false){
											Instruction* IL = checkEndOFLoad(I);
											if(isReplace == false){
												insertLibCallAfter(V, IL, ADDPAC);
												++addPAC_count;
											}
											else{
												replaceWithSignedPointer(IL, LI, V);
											}

										}
									}
									else if(V == VI && isCheckIfStore == 1 && isa<AllocaInst>(LII->getPointerOperand())){
										if(isReplace == false){
											insertLibCallAfter(V, I, ADDPAC);
											++addPAC_count;
										}
										else{
											replaceWithSignedPointer(I, LI, V);
										}
									}
								}
							}
							else if (StoreInst* SI = dyn_cast<StoreInst>(*AddPIt)){
								bool noInstrument = false;
								Value *VRHS = SI->getValueOperand();
								Value* V = SI->getPointerOperand();

								if (GetElementPtrInst* GRHS = dyn_cast<GetElementPtrInst>(VRHS)){
									Type* TyGRHS = GRHS->getResultElementType();
									if (shouldProtectType(TyGRHS)){
										if(LoadInst* LIGRHS = dyn_cast<LoadInst>(GRHS->getPointerOperand())){
											Value* VLIGRHS = LIGRHS->getPointerOperand();
											if(V != VLIGRHS){
												++addPAC_count;
												insertLibCallAfter(V, I, ADDPAC);
											}

											if(isReplace == false){
												++addPAC_count;
												insertLibCallAfter(VLIGRHS, I, ADDPAC);
											}
											else{
												replaceWithSignedPointer(I, LIGRHS, VLIGRHS);
											}
											continue;
										}
										else if(BitCastInst* BRHS = dyn_cast<BitCastInst>(GRHS->getPointerOperand())){
											if(LoadInst* LIBRHS = dyn_cast<LoadInst>(BRHS->getOperand(0))){
												Value* VBRHS = LIBRHS->getPointerOperand();
												if(V != VBRHS){
													++addPAC_count;
													insertLibCallAfter(V, I, ADDPAC);
												}
												if(isReplace == false){
													++addPAC_count;
													insertLibCallAfter(VBRHS, I, ADDPAC);
												}
												else{
													replaceWithSignedPointer(I, LIBRHS, VBRHS);
												}
												continue;
											}
										}
									}
								}
					
								if(StoreInst *SII = dyn_cast<StoreInst>(I)){
									Value* VS = SII->getPointerOperand();
									Value* VSI = SII->getValueOperand();
									if(LoadInst* LIInd = dyn_cast<LoadInst>(VS))
									{
										V = LIInd->getPointerOperand();
									}
									else if (I->getNextNode()->getName() == "gep_load"){
										Instruction* LastGEP = checkEndOFGEP(I->getNextNode());
										insertLibCallBefore(V, LastGEP, ADDPAC);
										++addPAC_count;
										break;
									}

									if(GetElementPtrInst* GI = dyn_cast<GetElementPtrInst>(V)){
										Value* VGEP = GI->getPointerOperand();
										if(isa<StructType>(GI->getSourceElementType())){
											if(shouldProtectType(SI->getPointerOperand()->getType())){
												CallInst* CL;
												if(Constant* C = dyn_cast<Constant>(VSI)){
													if(C->isNullValue()){
														if(!noInstrument){
															break;
														}
													}
													else{
														if(!noInstrument){
															CL = insertLibCallAfter(V, I, ADDPAC);
															++addPAC_count;
														}
													}
												}
												else{
													if(!noInstrument){
														CL = insertLibCallAfter(V, I, ADDPAC);
														++addPAC_count;
													}
												}
												if (!noInstrument){
													break;
												}
												else{ 
													recursiveStructInsertions(V, VGEP, I, ADDPAC);
												}
											}
											else {
												recursiveStructInsertions(V, VGEP, cast<Instruction>(SI), ADDPAC);
											}
											break;
										}

										else if(LoadInst* GLI = dyn_cast<LoadInst>(GI->getPointerOperand())){
											Value* VGLI = GLI->getPointerOperand();
											if(!noInstrument){

												if(isReplace == false){
													insertLibCallAfter(VGLI, I, ADDPAC);
													++addPAC_count;
												}
												else{
													replaceWithSignedPointer(I, GLI, VGLI);
												}
											}
										}
									}

									if(Constant* C = dyn_cast<Constant>(VSI)){
										if(C->isNullValue()){
											break;
										}
										else{
											if(!noInstrument){
												insertLibCallAfter(V, I, ADDPAC);
												++addPAC_count;
											}
										}
									}
									else{
										if(!noInstrument){
											insertLibCallAfter(V, I, ADDPAC);
											++addPAC_count;
										}
									}
								}
							}
							
							// Handling memcpy
							else if (CallInst* CI = dyn_cast<CallInst>(*AddPIt)){
								Function* CF = CI->getCalledFunction();
								if (isMemcpyFunction(CF->getName())){
									++numPACMemcpy;
									Value* src = CI->getArgOperand(1);
									Value* dest = CI->getArgOperand(0);
									Type* realSrcType = getOperandRealType(src);
									Type* realDestType = getOperandRealType(dest);
									if (shouldProtectType(realDestType)){
										if (BitCastInst* BCIdest = dyn_cast<BitCastInst>(dest)){
											if (GetElementPtrInst* GEPdest = dyn_cast<GetElementPtrInst>(BCIdest->getOperand(0))){
												if(LoadInst* LIdest = dyn_cast<LoadInst>(GEPdest->getPointerOperand())){
													insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
												}
											}
											else if (LoadInst* LIdest = dyn_cast<LoadInst>(BCIdest->getOperand(0))){
													insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
											}
										}
										else if (LoadInst* LIdest = dyn_cast<LoadInst>(dest)){
											insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
											++addPAC_count;
										}
									}

									if (shouldProtectType(realSrcType)){
										if (BitCastInst* BCIsrc = dyn_cast<BitCastInst>(src)){
											if (GetElementPtrInst* GEPsrc = dyn_cast<GetElementPtrInst>(BCIsrc->getOperand(0))){
												if(LoadInst* LIsrc = dyn_cast<LoadInst>(GEPsrc->getPointerOperand())){
													insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
												}
											}
											else if (LoadInst* LIsrc = dyn_cast<LoadInst>(BCIsrc->getOperand(0))){
													insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
											}
										}
										else if (LoadInst* LIsrc = dyn_cast<LoadInst>(src)){
											insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
											++addPAC_count;
										}
									}
								}
							}
						}
					}
				}
			}
		}

		// Instrument AddPACDeref values
		void instrumentAddPACDeref(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto AddPACDIt = AddPACDerefValues.begin(); AddPACDIt != AddPACDerefValues.end(); ++AddPACDIt){
						if(I == *AddPACDIt){
							CallInst* CI = dyn_cast<CallInst>(*AddPACDIt);
							Value* V = CI->getCalledOperand();		
							if(LoadInst *LI = dyn_cast<LoadInst>(V)){
								Value* VS = LI->getPointerOperand();
								if(LoadInst *LII = dyn_cast<LoadInst>(VS)){
									Value* VSS = LII->getPointerOperand();
									insertLibCallAfter(VSS, I, ADDPAC);
									++addPAC_count;
								}

								else if (GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(VS)){
									Value* VGEP = GI->getPointerOperand();
									if(isa<StructType>(GI->getSourceElementType())){
										CallInst* CL = insertLibCallAfter(VS, I, ADDPAC);
										++addPAC_count;
										recursiveStructInsertions(VS, VGEP, cast<Instruction>(CL), ADDPAC);
									}

									else if (LoadInst *GLI = dyn_cast<LoadInst>(VGEP)){
										Value* VGLI = GLI->getPointerOperand();
										insertLibCallAfter(VGLI, I, ADDPAC);
										++addPAC_count;
										insertLibCallAfter(VS, I, ADDPAC);
										++addPAC_count;
									}
									else {
										insertLibCallAfter(VS, I, ADDPAC);
										++addPAC_count;
									}
								}
								else {
									insertLibCallAfter(VS, I, ADDPAC);
									++addPAC_count;
								}
							}
							

							else if(BitCastInst* BI = dyn_cast<BitCastInst>(V)){
								Value* VB = BI->getOperand(0);
								if (LoadInst *BLI = dyn_cast<LoadInst>(VB)){
									Value* VBLI = BLI->getPointerOperand();
									if (GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(VBLI)){
										Value* VGEP = GI->getPointerOperand();
										if(isa<StructType>(GI->getSourceElementType())){
											CallInst* CL = insertLibCallAfter(VBLI, I, ADDPAC);
											++addPAC_count;
											recursiveStructInsertions(VBLI, VGEP, cast<Instruction>(CL), ADDPAC);
										}
										else if (LoadInst *GLI = dyn_cast<LoadInst>(VGEP)){
											Value* VGLI = GLI->getPointerOperand();
											insertLibCallAfter(VGLI, I, ADDPAC);
											++addPAC_count;
											insertLibCallAfter(VBLI, I, ADDPAC);
											++addPAC_count;
										}
										else {
											insertLibCallAfter(VBLI, I, ADDPAC);
											++addPAC_count;
										}
									}
								}
							}
						}
					}
				}
			}
		}

		// Instrument AuthPAC values
		void instrumentAuthPAC(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto AuthPIt = AuthPACValues.begin(); AuthPIt != AuthPACValues.end(); ++AuthPIt){
						if(I == *AuthPIt){
							if (LoadInst* LI = dyn_cast<LoadInst>(*AuthPIt)){
								Value* V = LI->getPointerOperand();
								if(V->getName() == "incdec.ptr"){
									if(GetElementPtrInst* GEPI = dyn_cast<GetElementPtrInst>(V)){
										if(LoadInst* LGI = dyn_cast<LoadInst>(GEPI->getPointerOperand())){
											Value* VLGI = LGI->getPointerOperand();
											if(ConstantInt *CI = dyn_cast<ConstantInt>(GEPI->getOperand(1))){
												insertLibCallAuth(VLGI, I, AUTHPAC, CI->getZExtValue());
												++authPAC_count;
											}
										}
									}
								}
								else if(Constant* C = dyn_cast<Constant>(V)){
									if(C->isNullValue()){
										break;	
									}
									else{
										insertLibCallAuth(V, I, AUTHPAC, 0);
										++authPAC_count;
									}
								}
								else{
									insertLibCallAuth(V, I, AUTHPAC, 0);
									++authPAC_count;
								}
																
								// Only for direct functions that have sensitive arguements
								for (const Use &UI : LI->uses()){
									auto I = cast<Instruction>(UI.getUser());
									if(BitCastInst* BI = dyn_cast<BitCastInst>(I)){
										if(CallInst* CI = dyn_cast<CallInst>(BI->getNextNode())){
											Function* CF = CI->getCalledFunction();
											if(CF && isReallocFunction(CF->getName())){
												insertLibCallAfter(V, CI, ADDPAC);
												++addPAC_count;
											}
										}
									}
									else if(isa<ICmpInst>(I)){
										continue;
									}
								}
							}
							else if (CallInst* CI = dyn_cast<CallInst>(*AuthPIt)){
								Value* VArg = CI->getArgOperand(0);
                            	if(GetElementPtrInst* GEPArg = dyn_cast<GetElementPtrInst>(VArg)){
                                Value* VGEPArg = GEPArg->getPointerOperand();
									if(ConstantInt *ConstI = dyn_cast<ConstantInt>(GEPArg->getOperand(1))){
										insertLibCallAuth(VGEPArg, I, AUTHPAC, ConstI->getZExtValue());
										++authPAC_count;
									}
								}
							}
						}
					}
				}
			}
		}

		// Instrument CPS Values
		void instrumentCPS(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					for (auto CPSIt = CPSValues.begin(); CPSIt != CPSValues.end(); ++CPSIt){
						if(I == *CPSIt){
							if(StoreInst* SI = dyn_cast<StoreInst>(*CPSIt)){
								Value* V = SI->getPointerOperand();
								Value* VS = SI->getValueOperand();
								if(LoadInst* LIInd = dyn_cast<LoadInst>(V)){
									V = LIInd->getPointerOperand();
								}
								if(Constant* C = dyn_cast<Constant>(VS)){
									if(C->isNullValue()){
										break;
									}
									else{
										insertLibCallAfter(V,I, ADDPAC);
										++addPAC_count;
									}
								}
								else{
									insertLibCallAfter(V,I, ADDPAC);
									++addPAC_count;
								}
							}
							else if (LoadInst* LI = dyn_cast<LoadInst>(*CPSIt)){
								Value* V = LI->getPointerOperand();
								insertLibCallAuth(V, I, AUTHPAC, 0);
								++authPAC_count;
							}
							else if (CallInst* CI = dyn_cast<CallInst>(*CPSIt)){
								Value* V = CI->getCalledOperand();
								Function* CF = CI->getCalledFunction();
								if(LoadInst* LI = dyn_cast<LoadInst>(V)){
									Value* VS = LI->getPointerOperand();
									if(LoadInst* LII = dyn_cast<LoadInst>(VS)){
										Value* VSS = LII->getPointerOperand();
										insertLibCallAfter(VSS, I, ADDPAC);
										++addPAC_count;
									}
									else if(isa<GetElementPtrInst>(VS)){
										insertLibCallAfter(VS, I, ADDPAC);
										++addPAC_count;
									}
									else {
										insertLibCallAfter(VS, I, ADDPAC);
										++addPAC_count;
									}
								}
								else if(BitCastInst* BI = dyn_cast<BitCastInst>(V)){
									Value* VB = BI->getOperand(0);
									if(LoadInst* BLI = dyn_cast<LoadInst>(VB)){
										Value* VBLI = BLI->getPointerOperand();
										insertLibCallAfter(VBLI, I, ADDPAC);
										++addPAC_count;
									}
								}

								else if (isMemcpyFunction(CF->getName())){
									Value* src = CI->getArgOperand(1);
									Value* dest = CI->getArgOperand(0);
									Type* realSrcType = getOperandRealType(src);
									Type* realDestType = getOperandRealType(dest);

									if (shouldProtectType(realDestType)){
										if (BitCastInst* BCIdest = dyn_cast<BitCastInst>(dest)){
											if (GetElementPtrInst* GEPdest = dyn_cast<GetElementPtrInst>(BCIdest->getOperand(0))){
												if(LoadInst* LIdest = dyn_cast<LoadInst>(GEPdest->getPointerOperand())){
													insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
												}
											}
											else if (LoadInst* LIdest = dyn_cast<LoadInst>(BCIdest->getOperand(0))){
													insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
											}
										}
										else if (LoadInst* LIdest = dyn_cast<LoadInst>(dest)){
											insertLibCallAfter(LIdest->getPointerOperand(), I, ADDPAC);
											++addPAC_count;
										}
									}

									if (shouldProtectType(realSrcType)){
										if (BitCastInst* BCIsrc = dyn_cast<BitCastInst>(src)){
											if (GetElementPtrInst* GEPsrc = dyn_cast<GetElementPtrInst>(BCIsrc->getOperand(0))){
												if(LoadInst* LIsrc = dyn_cast<LoadInst>(GEPsrc->getPointerOperand())){
													insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
												}
											}
											else if (LoadInst* LIsrc = dyn_cast<LoadInst>(BCIsrc->getOperand(0))){
													insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
													++addPAC_count;
											}
										}
										else if (LoadInst* LIsrc = dyn_cast<LoadInst>(src)){
											insertLibCallAfter(LIsrc->getPointerOperand(), I, ADDPAC);
											++addPAC_count;
										}
									}
								}
							}
							else {
								outs() << "INVALID CPS INSTRUCTION\n";
							}
						}
					}
				}
			}
		}

		// Instrument removeMetadata
		void instrumentRemoveMeta(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					// Instrument removeMetadata for heap
					for (auto removeMetaIt = removeMetaValues.begin(); removeMetaIt != removeMetaValues.end(); ++removeMetaIt){
						if(I == *removeMetaIt){
							if(CallInst* CI = dyn_cast<CallInst>(I)){
								Value* VC = CI->getArgOperand(0);
								if(BitCastInst* BI = dyn_cast<BitCastInst>(VC)){
									Value* VB = BI->getOperand(0);
									if(LoadInst* LI = dyn_cast<LoadInst>(VB)){
										Value* V = LI->getPointerOperand();
										insertLibCallBefore(V, I, REMOVEMETA);
										++removeMeta_count;
									}
								}
								else if (LoadInst* LI = dyn_cast<LoadInst>(VC)){
									Value* V = LI->getPointerOperand();
									insertLibCallBefore(V, I, REMOVEMETA);
									++removeMeta_count;
								}
								else if(isa<ConstantExpr>(CI->getCalledOperand())){
									Value* VCE = CI->getOperand(0);
									if(BitCastInst* BI = dyn_cast<BitCastInst>(VCE)){
										Value* VB = BI->getOperand(0);
										if(LoadInst* LI = dyn_cast<LoadInst>(VB)){
											Value* V = LI->getPointerOperand();
											insertLibCallBefore(V, I, REMOVEMETA);
											++removeMeta_count;
										}
									}
									else if (LoadInst* LI = dyn_cast<LoadInst>(VCE)){
										Value* V = LI->getPointerOperand();
										insertLibCallBefore(V, I, REMOVEMETA);
										++removeMeta_count;
									}
								}
							}
						}
					}
					// Instrument removeMetadata for stack
					if(isa<ReturnInst>(I)){
						for (auto SetMt = SetMetaValues.begin(); SetMt != SetMetaValues.end(); ++SetMt){
							if(F.getName() == SetMt->second.function){
								if(AllocaInst* AI = dyn_cast<AllocaInst>(SetMt->first)){
									Value* V = &*AI;
									insertLibCallBefore(V, I, REMOVEMETASTACK);
									++removeMeta_count;
								}
							}
						}
					}
				}
			}
		}

		//Instrument globals
		void instrumentGlobals (Module &M){
			LLVMContext &C = M.getContext();
			Function* FSetMeta = Function::Create(FunctionType::get(Type::getVoidTy(C), false), GlobalValue::InternalLinkage, "globalInstrument", &M);
			BasicBlock* Entry = BasicBlock::Create(C, "entry", FSetMeta);
			IRBuilder<> builder(C);
			builder.SetInsertPoint(Entry);
			builder.CreateRetVoid();

			for (auto &F : M) {
				for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
					BasicBlock *BB = &*FIt;
					for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
						Instruction *I = &*BBIt;
						// Instrument globals
						if (!globalsInstrumented){
							for (auto GIt = M.global_begin(); GIt != M.global_end(); ++GIt){
								GlobalVariable* GV = dyn_cast<GlobalVariable>(&*GIt);
								if(GV && GV->hasInitializer()){
									++numInitStores;
									Type* Ty = GV->getInitializer()->getType();
									DataLayout DL = DataLayout(I->getModule());
									int typeSize = DL.getTypeAllocSize(Ty);
									if(isCPS){
										if(shouldProtectTypeFP(Ty) && !GV->getName().startswith("llvm.") && !GV->getName().startswith("__")){
											++numPACInitStores;
										}
									}
									else {
										if(shouldProtectType(Ty) && !GV->getName().startswith("llvm.") && !GV->getName().startswith("__")) {
											if(PointerType* PTy = dyn_cast<PointerType>(Ty)){
												Ty = PTy->getElementType();
											}
											++numPACInitStores;
											if (ArrayType *ATy = dyn_cast<ArrayType>(Ty)){
												unsigned int numElements = ATy->getNumElements();
												for (unsigned int i = 0; i < numElements; i++){
													Value* V = insertGEP(I->getNextNode(), i, ATy, GV);
													if(Constant* C = dyn_cast<Constant>(V)){
														if(C->isNullValue()){
															break;
														}
														else{
															insertLibCallAfter(V, I, ADDPAC);
															++addPAC_count;
														}

													}
													else{
														insertLibCallAfter(V, I, ADDPAC);
														++addPAC_count;
													}
													insertSetMetaLibCall(V, I, SETMETAOBJ, numElements, typeSize);
													++setMeta_count;
												}
											}
											
											else{												
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
												FunctionCallee Func = M.getOrInsertFunction(SETMETAOBJ, FTy);
												ArrayRef<Value*> FuncArgs = {
													builder.CreatePointerCast(GV, Ty->getPointerTo()),
													NumElements,
													TypeSize
												};
												
												FunctionType* FTy1 = FunctionType::get(ResultFTy, FuncParams1, false);
												FunctionCallee Func1 = M.getOrInsertFunction(ADDPAC, FTy1);
												ArrayRef<Value*> FuncArgs1 = {
                                                    							builder.CreatePointerCast(GV, Ty->getPointerTo())
                                                						};
												
												builder.CreateCall(Func, FuncArgs);
												builder.CreateCall(Func1, FuncArgs1);
											}
										}
									}
								}
							}
							appendToGlobalCtors(M, FSetMeta, 0);
							globalsInstrumented = true;
							outs() << "####GLOBALS####\n";	
						}
					}		
				}
			}
		}
		
		// Handles structs with the replace function
		void recursiveStructReplaceInsertions(Value* VS, Value* VGEP, Instruction* I){
			if (LoadInst *GLI = dyn_cast<LoadInst>(VGEP)){
				Value* VGLI = GLI->getPointerOperand();
				CallInst* CL = replaceWithSignedPointer(I, GLI, VGLI);
				
				if (GetElementPtrInst* VGI = dyn_cast<GetElementPtrInst>(VGLI)){
					recursiveStructReplaceInsertions(VGI, VGI->getPointerOperand(), cast<Instruction>(CL));
				}
			}

			else if (GetElementPtrInst *GGI = dyn_cast<GetElementPtrInst>(VGEP)){
				recursiveStructReplaceInsertions(GGI, GGI->getPointerOperand(), I);
			}

			else if (BitCastInst *BI = dyn_cast<BitCastInst>(VGEP)){
				if(shouldProtectType(BI->getSrcTy())){
					if (LoadInst *GLI = dyn_cast<LoadInst>(BI->getOperand(0))){
						Value* VGLI = GLI->getPointerOperand();
						CallInst* CL = replaceWithSignedPointer(I, GLI, VGLI);

						if (GetElementPtrInst* VGI = dyn_cast<GetElementPtrInst>(VGLI)){
							recursiveStructReplaceInsertions(VGI, VGI->getPointerOperand(), cast<Instruction>(CL));
						}
					}

					else if (GetElementPtrInst *GGI = dyn_cast<GetElementPtrInst>(VGEP)){
						recursiveStructReplaceInsertions(GGI, GGI->getPointerOperand(), I);
					}
				}
			}
		}

		// Takes two arguments for the replaceWithSigned library.
		CallInst* insertReplaceLibCall(Value* ArgVal, Value* ArgVal_sign, Instruction* InsertPointInst, StringRef FunctionName){
			LLVMContext &C = InsertPointInst->getFunction()->getContext();
			IRBuilder<> builder(C);

			Type* Ty = Type::getInt8Ty(C)->getPointerTo();
			// Insertion point after passed instruction
			builder.SetInsertPoint(InsertPointInst->getNextNode());

			ArrayRef<Type*> FuncParams = {
				Ty->getPointerTo(),
				Ty->getPointerTo()
			};

			Type* ResultFTy = Type::getVoidTy(C);
			FunctionType* FTy = FunctionType::get(ResultFTy, FuncParams, false);

			FunctionCallee Func = InsertPointInst->getModule()->getOrInsertFunction(FunctionName, FTy);
			Value* Addr = builder.Insert(CastInst::CreatePointerCast(ArgVal, Ty->getPointerTo(),""));
			Value* Addr_sign = builder.Insert(CastInst::CreatePointerCast(ArgVal_sign, Ty->getPointerTo(),""));
			ArrayRef<Value*> FuncArgs = {
				Addr,
				Addr_sign
			};

			return builder.CreateCall(Func, FuncArgs);
		}

		// Inserts the replaceWithSignedPointer Function. V is the pointer that is replaced with the PACed.
		CallInst* replaceWithSignedPointer(Instruction* insertPoint, LoadInst* LI, Value* V){
			if(LI->getPrevNonDebugInstruction() != nullptr){
				if(CallInst *AuthC = dyn_cast<CallInst>(LI->getPrevNonDebugInstruction())){
					Function* CF = AuthC->getCalledFunction();
					if(CF){
						StringRef S = CF->getName();
						if(S.equals("authenticatePAC")){
							Value* authV = AuthC->getArgOperand(0);
							if(Instruction* authVI = dyn_cast<Instruction>(authV)){
								Value* authVL = insertLoad(authVI, authV);
								CallInst* CLR = insertReplaceLibCall(V, authVL, insertPoint, REPLACESIGN);
								++numReplace_count;
								return CLR;
							}
						}
					}
				}
			}
			return nullptr;
		}

		// Instrumentation to replace pointers with PACed pointers after load.
		void replaceWithSignedPointerInstrumentation(Function& F){
			for (Function::iterator FIt = F.begin(); FIt != F.end(); ++FIt){
				BasicBlock *BB = &*FIt;
				for (BasicBlock::iterator BBIt = BB->begin(); BBIt != BB->end(); ++BBIt){
					Instruction *I = &*BBIt;
					if (CallInst *CI = dyn_cast<CallInst>(I)){
						Function *CF = CI->getCalledFunction();
						if (CF && isLLVMFunction(CF->getName())){
							continue;
						}
						if (CI->isTailCall()){
							continue;
						}

						if (CI->isIndirectCall()){
							Value* V = CI->getCalledOperand();
							if(LoadInst* LI = dyn_cast<LoadInst>(V)){
								Value* VS = LI->getPointerOperand();
								if(LoadInst* LII = dyn_cast<LoadInst>(VS)){
									Value *VSS = LII->getPointerOperand();
									replaceWithSignedPointer(I, LII, VSS);
								}
								else if(GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(VS)){
									Value* VGEP = GI->getPointerOperand();
									if(isa<StructType>(GI->getSourceElementType())){
										CallInst* CL = replaceWithSignedPointer(I, LI, VS);
										recursiveStructReplaceInsertions(VS, VGEP, cast<Instruction>(CL));
									}
									else if (LoadInst* GLI = dyn_cast<LoadInst> (VGEP)){
										Value* VGLI = GLI->getPointerOperand();
										replaceWithSignedPointer(I, GLI, VGLI);
										replaceWithSignedPointer(I, LI, VS);
									}
									else{
										replaceWithSignedPointer(I, LI, VS);
									}
								}
								else{
									replaceWithSignedPointer(I, LI, VS);
								}
							}
							else if(BitCastInst* BI = dyn_cast<BitCastInst>(V)){
								Value* VB = BI->getOperand(0);
								if(LoadInst* BLI = dyn_cast<LoadInst>(VB)){
									Value* VBLI = BLI->getPointerOperand();
									if(GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(VBLI)){
										Value* VGEP = GI->getPointerOperand();
										if(isa<StructType>(GI->getSourceElementType())){
											CallInst* CL = replaceWithSignedPointer(I, BLI, VBLI);
											recursiveStructReplaceInsertions(VBLI, VGEP, cast<Instruction>(CL));
										}
										else if(LoadInst *GLI = dyn_cast<LoadInst>(VGEP)){
											Value* VGLI = GLI->getPointerOperand();
											replaceWithSignedPointer(I, GLI, VGLI);
											replaceWithSignedPointer(I, BLI, VBLI);
										}
										else{
											replaceWithSignedPointer(I, BLI, VBLI);
										}
									}
								}
							}
						}
					}
				}
			}
		}

		
		bool runOnModule (Module &M) override {
			// Check for all legitimate indirect functions used by the program
			checkIndFunction(M);

			for (auto &F : M) {
				// Skip LLVM functions.
				if (isLLVMFunction(F.getName()) && !F.isDeclaration()){
					continue;
				}

				// Start checking each function and finding sensitive pointers
				checkFunction(F);
				
				// Instrumentation of sensitive pointers found.
				if(isCPS){
					instrumentCPS(F);
				}
				instrumentAddPAC(F);
				instrumentSetMeta(F);
				instrumentSetMetaInd(F);
				if(isReplace == false){
					instrumentAddPACDeref(F);
				}
				instrumentAuthPAC(F);
				instrumentRemoveMeta(F);
				if(isReplace == true){
					replaceWithSignedPointerInstrumentation(F);
				}
			}
			outs() << "PACTight Statistics\n";
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
			printStat(outs(), numReplace_count);

			return true;
		}

		bool isLLVMFunction(StringRef s){
			return s.startswith("llvm.") || s.startswith("__llvm__");
		}

		bool isMallocFunction(StringRef s){
			return s.equals("malloc");
		}

		bool isFreeFunction(StringRef s){
			return s.equals("free");
		}

		bool isCallocFunction(StringRef s){
			return s.equals("calloc");
		}

		bool isReallocFunction(StringRef s){
			return s.equals("realloc");
		}

		bool isMemcpyFunction(StringRef s){
			return s.startswith("llvm.memcpy");
		}
		
		bool isMmapFunction(StringRef s){
			return s.equals("mmap");
		}

		bool isMunmapFunction(StringRef s){
			return s.equals("munmap");
		}

		bool isAllocLibFunction(StringRef s){
			return isMallocFunction(s) || isCallocFunction(s) || isReallocFunction(s) || isMmapFunction(s);
		}

		bool isDeallocLibFunction(StringRef s){
			return isFreeFunction(s) || isMunmapFunction(s);
		}
	};
}

char DVIPACPass::ID = 0;
INITIALIZE_PASS(DVIPACPass, // Name of pass class, e.g., MyAnalysis
        "dvi-pac", // Command-line argument to invoke pass
        "DVI PAC implementation", // Short description of pass
        false, // Does this pass modify the control-flow graph?
        false) // Is this an analysis pass?

namespace llvm {
    ModulePass *createDVIPACPass() {
        return new DVIPACPass();
    }
}

