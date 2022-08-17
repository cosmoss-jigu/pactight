#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/mman.h>

typedef struct {
	unsigned long tag; //64-bit
	//unsigned int tag; //32-bit
	unsigned long nElements;
	int typeSize;
} __attribute__((packed)) metadata;

#define SIZE ((0x1 << 28) * sizeof(unsigned long))
#define MAPPING_PATTERN ((SIZE - 1) ^ (sizeof(unsigned long) -1))
#define SHIFT_BITS 2
#define GET_OFFSET(addr) ((((uintptr_t)(addr)) << SHIFT_BITS) & MAPPING_PATTERN)

__attribute__((visibility("default")))
extern void init_memory();
__attribute__((visibility("default")))
extern void dvipac_set(void **fptr, unsigned long tag, unsigned int nElements, int typeSize); //64-bit
//extern void dvipac_set(void **fptr, unsigned int tag, unsigned int nElements, int typeSize); //32-bit
__attribute__((visibility("default")))
extern metadata* dvipac_get(void **fptr);
__attribute__((visibility("default")))
extern void dvipac_remove(void **fptr);

metadata *shadow_memory;
