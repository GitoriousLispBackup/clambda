#include "../../../libguile.h"

#define SCM_DEFINE(f,s,a,b,c,arg,str) inline SCM f arg
#define SCM_API 

#include "../../../libguile/unify.h"
#include "../../../libguile/unify.c"

#define  c_scm(x)     smob2scm(x)
#define  c_var()      gp_mkvar()
#define  c_newframe() gp_gp_newframe()
#define  c_unwind(p)  gp_gp_unwind(p)
#define  c_unify(x,y) gp_gp_unify_raw(x,y)
#define  c_lookup(x)  gp_gp_lookup(x)
#define  c_pair(x)    gp_pair_bang(x)
#define  c_pair2(x)   gp_pair2(x)
#define  c_car(x)     gp_car(x)
#define  c_cdr(x)     gp_gp_cdr(x)
#define  c_cons(x,y)  gp_cons_bang(x,y)

typedef void * (* tail__fkn)(SCM *,SCM *);

#define assert__stack(x,y) x
#define free__frame(x) 
#define AREF(x,i) (x)[i]
#define TAILFKN(x) ((tail__fkn) (x))
/* The macros below check the CPU's overflow flag to improve fixnum
   arithmetic.  The %rcx register is explicitly clobbered because `asm
   goto' can't have outputs, in which case the `r' constraint could be
   used to let the register allocator choose a register.

   TODO: Use `cold' label attribute in GCC 4.6.
   http://gcc.gnu.org/ml/gcc-patches/2010-10/msg01777.html  */

inline SCM ASM_ADD(SCM x, SCM y)					       
{
  SCM sp[1];
  {
    asm volatile goto ("mov %1, %%rcx; "
		       "test %[tag], %%cl; je %l[slow_add]; "
		       "test %[tag], %0;   je %l[slow_add]; "
		       "add %0, %%rcx;     jo %l[slow_add]; "
		       "sub %[tag], %%rcx; "
		       "mov %%rcx, (%[vsp])\n"			
		       : /* no outputs */
		       : "r" (x), "r" (y),
			 [vsp] "r" (sp), [tag] "i" (scm_tc2_int)
		       : "rcx", "memory"
		       : slow_add);
    return sp[0];
  }
 slow_add: 
  return scm_sum(x,y);
}

inline SCM ASM_SUB(SCM x, SCM y)
{
  SCM sp[1];
  {
    asm volatile goto ("mov %0, %%rcx; "
		       "test %[tag], %%cl; je %l[slow_sub]; "
		       "test %[tag], %1;   je %l[slow_sub]; "
		       "sub %1, %%rcx;     jo %l[slow_sub]; "
		       "add %[tag], %%rcx; "
		       "mov %%rcx, (%[vsp])\n"
		       : /* no outputs */
			 : "r" (x), "r" (y),
			   [vsp] "r" (sp), [tag] "i" (scm_tc2_int)
		       : "rcx", "memory"
		       : slow_sub);
    return sp[0];
  }
 slow_sub:
  return scm_difference(x,y);
}

