#include "kmod_alloc.h"
#include <linux/slab.h> // contains kzalloc, kmalloc_array and kfree.

void * alloc(size_t sz)
{
  return kzalloc(sz, GFP_KERNEL);
}

void * alloc_array(size_t n, size_t sz)
{
  return kmalloc_array(n, sz, GFP_KERNEL);
}

void free(const void *objp)
{
  kfree(objp);
}