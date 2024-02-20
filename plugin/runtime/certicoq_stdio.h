/* This file declares stdio functionality depending on
 * whether this file is compiled for Linux Kernel
 * or regular user space programs.
 * Additionally it exposes the macro trace(...)
 * that calls printk with log level KERN_INFO in Kernel space
 * and printf in user space if CERTICOQ_TRACE is defined and
 * is a nop, else.
 */

#ifndef CERTICOQ_STDIO_H
#define CERTICOQ_STDIO_H

#ifdef CLIGHT_KERNEL_CODE
  #include <linux/printk.h>
  #ifdef CERTICOQ_TRACE
    #define trace(...) printk(KERN_INFO __VA_ARGS__)
  #else
    #define trace(...) //printk(KERN_INFO __VA_ARGS__)
  #endif
#else
  #include <stdio.h>
  #ifdef CERTICOQ_TRACE
    #define trace(...) printf(__VA_ARGS__)
  #else
    #define trace(...) //printf(__VA_ARGS__)
  #endif
#endif

#endif // CERTICOQ_STDIO_H