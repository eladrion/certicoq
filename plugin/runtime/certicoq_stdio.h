/* This file declares stdio functionality depending on
 * whether this file is compiled for Linux Kernel
 * or regular user space programs.
 * Additionally it exposes the macro trace(...)
 * that calls printk with log level KERN_INFO in Kernel space
 * and printf in user space.
 */

#ifndef CERTICOQ_GC_STDIO_H
#define CERTICOQ_GC_STDIO_H

#ifdef CLIGHT_KERNEL_CODE
  #include <linux/printk.h>
  #define trace(...) printk(KERN_INFO __VA_ARGS__)
#else
  #include <stdio.h>
  #define trace(...) printf(__VA_ARGS__)
#endif

#endif // CERTICOQ_GC_STDIO_H