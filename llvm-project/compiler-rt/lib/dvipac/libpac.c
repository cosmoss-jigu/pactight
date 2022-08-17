#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
//#include <sys/prctl.h>
#include <stdint.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>
#include <stdbool.h>
#include "libpac.h"
#define PAC
//#define PACINST
#define EOR
#define PACEXISTS
#define bitGet(value) (value >> 48)

// Function to add PAC to a pointer.
void addPAC (void** p) {
#ifdef PACEXISTS
	if(bitGet((unsigned long long) *p)){
        	return;
    	}
#endif

#ifdef PAC
	metadata* meta = dvipac_get(*p);
	if (!meta->tag)
	{
		dvipac_set(*p, 23, 1, 8);
	}

	unsigned long mod; //64-bit
	mod = meta->tag;
	
#ifdef PACINST
	__asm volatile ("pacia %x[pointer], %x[modifier]\n"
			: [pointer] "+r" (*p)
			: [modifier] "r"(mod)
			);
#endif
#ifdef EOR
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
#endif
#endif
}

// Function to authenticate PAC to a pointer.
void authenticatePAC (void** p, unsigned int n) {
#ifdef PACEXISTS
	if(!bitGet((unsigned long long) *p)){
		return;
    	}
#endif
#ifdef PAC
	metadata* meta = dvipac_get(*p + n);
	if (!meta->tag)
	{
		dvipac_set(*p + n, 23, 1, 8);
	}
	unsigned long mod; //64-bit
	mod = meta->tag;
#ifdef PACINST
	__asm volatile ("autia %x[pointer], %x[modifier]\n"
			: [pointer] "+r" (*p)
			: [modifier] "r"(mod) 
			);
#endif
#ifdef EOR
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
    __asm volatile ("eor x18, x18, x18\n");
#endif
#endif
}


// Function that inserts metadata into the hashtable.
void setMetadata(void* p, unsigned int nElements, int typeSize){
#ifdef PAC
	if (metadataExists(p))
	{
		return;
	}	
	unsigned long tag; //64-bit
	tag = 23;
	dvipac_set(p, tag, nElements, typeSize);
#endif
}

// Function that inserts metadata into the hashtable.
void setMetadataObj(void** p, unsigned int nElements, int typeSize){
#ifdef PAC
	if (metadataExists(*p))
	{
		return;
	}	
	unsigned long tag; //64-bit
	tag = 23;
	dvipac_set(*p, tag, nElements, typeSize);
#endif
}

// Function that removes metadata from the hashtable.
void removeMetadata(void** p){
#ifdef PAC
	metadata* meta = dvipac_get(*p);
	if (!meta->tag)
	{
		return;	
	}
	unsigned nElements = meta->nElements;
	unsigned typeSize = meta->typeSize;
	for(int i = 0; i < nElements; i++){
		dvipac_remove(*p);
		(*p) = (*p) + typeSize;
	}
#endif
}

// Function that removes metadata from the hashtable.
void removeMetadataStack(void* p){
#ifdef PAC
	metadata* meta = dvipac_get(p);
	if (!meta->tag)
	{
		return;
	}
	unsigned nElements = meta->nElements;
	unsigned typeSize = meta->typeSize;
	for(int i = 0; i < nElements; i++){
		dvipac_remove(p);
		(p) = (p) + typeSize;
	}
#endif
}

// Function that detects if metadata exists.
bool metadataExists(void* p){
#ifndef PAC
	if (p){
		return false;
	}
	else{
		return true;
	}
#endif
#ifdef PAC
	metadata* meta = dvipac_get(p);
	if (!meta->tag){
		return false;
	}
	else{
		return true;
	}
#endif
}

// Function that replaces pointer with already PACed pointer
void replaceWithSignedPointer(void** p, void* signed_p){

#ifdef PACEXISTS
	if(!bitGet((unsigned long long) signed_p)){
        	return;
    	}
#endif

	*p = signed_p;
}
