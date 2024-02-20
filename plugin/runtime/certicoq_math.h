/* This file declares math functionality depending on
 * whether this file is compiled for Linux Kernel
 * or regular user space programs.
 * This file is necessary when using functions like abs().
 */

#ifndef CERTICOQ_MATH_H
#define CERTICOQ_MATH_H

#ifdef CLIGHT_KERNEL_CODE
 // Definitions for use when compiling for Linux Kernel modules
 #include <linux/math.h>
#else // !CLIGHT_KERNEL_CODE
 // For userland code, load the libc stdint.
 #include <math.h>
#endif // CLIGHT_KERNEL_CODE

#endif // CERTICOQ_MATH_H