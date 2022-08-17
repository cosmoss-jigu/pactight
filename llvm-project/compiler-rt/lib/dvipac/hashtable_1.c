#include "hashtable_1.h"


void __attribute__((constructor)) init_memory()
{
	
	unsigned long long size = SIZE;

	void *p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);

	if (p == (void*)-1){
		perror("Failed to mmap.");
		exit(1);
	}

	if(shadow_memory)
		return;

	shadow_memory = (metadata*) p;
}


void dvipac_set(void **fptr, unsigned long tag, unsigned int nElements, int typeSize) //64-bit
{
	unsigned long offset = GET_OFFSET(fptr) + sizeof(unsigned long) & (SIZE -1);
	metadata *ptr = ((metadata *)(((unsigned char*) shadow_memory) + offset));
	ptr->tag = tag;
	ptr->nElements = nElements;
	ptr->typeSize = typeSize;
}

metadata* dvipac_get(void **fptr)
{
	unsigned long offset = GET_OFFSET(fptr) + sizeof(unsigned long) & (SIZE -1);
	metadata *ptr = ((metadata *)(((unsigned char*) shadow_memory) + offset));
	return ptr;
}


void dvipac_remove(void **fptr)
{
	unsigned long offset = GET_OFFSET(fptr) + sizeof(unsigned long) & (SIZE -1);
	metadata *ptr = ((metadata *)(((unsigned char*) shadow_memory) + offset));
	ptr->tag = 0;
	ptr->nElements = 0;
	ptr->typeSize = 0;
}
