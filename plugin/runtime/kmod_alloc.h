#ifndef CERTICOQ_KMOD_ALLOC_H
#define CERTICOQ_KMOD_ALLOC_H

#include <linux/types.h> // For types

void * alloc(size_t sz);

void * alloc_array(size_t n, size_t sz);

void free(const void *ptr);

#endif // CERTICOQ_KMOD_ALLOC_H