#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <stdint.h>
#include "hashtable_1.h"

__attribute__((visibility("default")))
extern void addPAC (void** p);
__attribute__((visibility("default")))
extern void authenticatePAC (void** p, unsigned int n);
__attribute__((visibility("default")))
extern void setMetadata(void* p, unsigned int nElements, int typeSize);
__attribute__((visibility("default")))
extern void setMetadataObj(void** p, unsigned int nElements, int typeSize);
__attribute__((visibility("default")))
extern void removeMetadata(void** p);
__attribute__((visibility("default")))
extern void removeMetadataStack(void* p);
__attribute__((visibility("default")))
extern bool metadataExists(void* p);
__attribute__((visibility("default")))
extern void replaceWithSignedPointer(void** p, void* signed_p);
