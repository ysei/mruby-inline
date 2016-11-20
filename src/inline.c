#include "mruby.h"
#include "mruby/class.h"
#include "mruby/value.h"
#include "mruby/variable.h"
#include "mruby/opcode.h"
#include "mruby/irep.h"
#include "mruby/hash.h"
#include "mruby/proc.h"
#include "opinfo.h"

static mrb_irep *
copy_irep(mrb_state *mrb, mrb_irep *irep)
{
  mrb_irep *nirep = mrb_add_irep(mrb);
  int i;

  *nirep = *irep;
  nirep->iseq = (mrb_code*)mrb_malloc(mrb, sizeof(mrb_code)*irep->ilen);
  for (i = 0; i < irep->ilen; i++) {
    nirep->iseq[i] = irep->iseq[i];
// i = 0
// while (i < irep->ilen) {
//  nirep->iseq[i] = irep->iseq[i++];	/* -O0 ? */
  }

  nirep->reps = (mrb_irep**)mrb_malloc(mrb, sizeof(mrb_irep*)*irep->rlen);
  for (i = 0; i < irep->rlen; i++) {
    nirep->reps[i] = copy_irep(mrb, irep->reps[i]);
// i = 0
// while (i < irep->rlen) {
//  nirep->reps[i] = copy_irep(mrb, irep->reps[i++]);	/* -O0 ? */
  }

  return nirep;
}

static void
patch_reps(mrb_state *mrb, mrb_irep *irep, int a, int level) {
  int i;

  for (i = 0; i < irep->ilen; i++) {
// i = 0
// while (i < irep->ilen) {
    mrb_code code = irep->iseq[i];
    switch (GET_OPCODE(code)) {
    case OP_GETUPVAR:
    case OP_SETUPVAR:
      if (level == GETARG_C(code)) {
	code = MKOP_ABC(GET_OPCODE(code), 
			GETARG_A(code), GETARG_B(code) + a, level);
	irep->iseq[i] = code;
//	irep->iseq[i++] = code;		/* -O0 ? */
      }

      break;

    default:
      /* Do nothing */
//    i++;				/* bunki yosoku ? */
      break;
    }
  }

  for (i = 0; i < irep->rlen; i++) {
    patch_reps(mrb, irep->reps[i], a, level + 1);
// i = 0
// while (i < irep->rlen) {
//  patch_reps(mrb, irep->reps[i++], a, level + 1);	/* -O0 ? */
  }
}

static mrb_code *
patch_irep_for_inline(mrb_state *mrb, mrb_irep *src, mrb_irep *dst, int a)
{
  mrb_code *send_pc;
  mrb_code *curpos;
  mrb_code *ent;
  mrb_code code;
// mrb_code get_opcode__code;			/* ? */
// mrb_code optype_list__get_opcode__code;	/* ? */
// mrb_code getarg_a__code;			/* ? */
// mrb_code getarg_a__code__a;			/* ? */
// mrb_code getarg_b__code;			/* ? */
// mrb_code getarg_b__code__a;			/* ? */
/// mrb_code getarg_bx__code;			/* ? */
// mrb_code getarg_c__code;			/* ? */
// mrb_code getarg_c__code__a;			/* ? */
  int i;
  size_t symbase = dst->slen;
  size_t poolbase = dst->plen;
  size_t repsbase = dst->rlen;
  size_t entpos;
  size_t pcoff;

  /* extend iseq */
  entpos = dst->ilen;
  pcoff = mrb->c->ci->pc - dst->iseq;
  dst->ilen += src->ilen + 2 + 1; /* 2 meta info 1 return(2word) */
  dst->iseq = mrb_realloc(mrb, dst->iseq, dst->ilen * sizeof(mrb_code));
#ifdef MRBJIT
  mrb_free(mrb, dst->prof_info);
  mrb_free(mrb, dst->jit_entry_tab);
  mrbjit_make_jit_entry_tab(mrb, dst, dst->ilen);
  dst->prof_info = (int *)mrb_calloc(mrb, dst->ilen, sizeof(int));
#endif
  send_pc =  dst->iseq + pcoff - 1;
  ent = dst->iseq + entpos;
// send_pc = dst->iseq;
// ent = send_pc + entpos;
// send_pc += pcoff - 1;
  curpos = ent;

  /* extend syms */
  if (src->slen > 0) {
    dst->slen += src->slen;
    dst->syms = mrb_realloc(mrb, dst->syms, dst->slen * sizeof(mrb_sym));
    for (i = 0; i < src->slen; i++) {
      dst->syms[symbase + i] = src->syms[i];
//  i = 0;
//  while (i < src->slen) {
//    dst->syms[symbase + i] = src->syms[i++];	/* -O0 ? */
    }
  }

  /* extend pool */
  if (src->plen > 0) {
    dst->plen += src->plen;
    dst->pool = mrb_realloc(mrb, dst->pool, dst->plen * sizeof(mrb_value));
    for (i = 0; i < src->plen; i++) {
      dst->pool[poolbase + i] = src->pool[i];
//  i = 0;
//  while (i < src->plen) {
//    dst->pool[poolbase + i] = src->pool[i++];		/* -O0 ? */
    }
  }

  /* extend reps */
  if (src->rlen > 0) {
    dst->rlen += src->rlen;
    dst->reps = mrb_realloc(mrb, dst->reps, dst->rlen * sizeof(mrb_irep *));
    for (i = 0; i < src->rlen; i++) {
      dst->reps[repsbase + i] = copy_irep(mrb, src->reps[i]);
//  i = 0;
//  while (i < src->rlen) {
//    dst->reps[repsbase + i] = copy_irep(mrb, src->reps[i++]);		/* -O0 ? */
    }
  }

  /* Meta data */
  *(curpos++) = MKOP_A(OP_NOP, src->ilen); /* size */
  *(curpos++) = MKOP_A(OP_NOP, src->ilen);
  *send_pc = MKOP_sBx(OP_JMP, curpos - send_pc);

  /* Patched inlined code */
  for (i = 0; i < src->ilen; i++) {
    code = src->iseq[i];
// i = 0;
// while (i < src->ilen) {
//  code = src->iseq[i++];	/* -O0 ? */

//  get_opcode__code  = GET_OPCODE(code);
//  getarg_a__code    = GETARG_A(code);
//  getarg_a__code__a = getarg_a__code + a;

    switch(GET_OPCODE(code)) {
//  switch(get_opcode__code)) {
    case OP_RETURN:
      code = MKOP_AB(OP_MOVE, a, GETARG_A(code) + a);
//    code = MKOP_AB(OP_MOVE, a, getarg_a__code__a);
      *(curpos++) = code;
      code = MKOP_sBx(OP_JMP, send_pc - curpos + 1);
      break;

    case OP_LOADSELF:
      code = MKOP_AB(OP_MOVE, GETARG_A(code), 0);
//    code = MKOP_AB(OP_MOVE, getarg_a__code, 0);
      break;

/// default:
///   switch(get_opcode__code)) {
      case OP_LAMBDA:
	code = MKOP_Abc(OP_LAMBDA, GETARG_A(code), GETARG_b(code) + repsbase, GETARG_c(code));
//	code = MKOP_Abc(OP_LAMBDA, getarg_a__code, GETARG_b(code) + repsbase, GETARG_c(code));
	patch_reps(mrb, dst->reps[GETARG_b(code)], a, 0);
	break;

      case OP_ENTER:
	code = MKOPCODE(OP_NOP);
	break;
///
///   }

    default:
      /* do nothing */
      break;
    }

    /* Shift regster number */
//  get_opcode__code = GET_OPCODE(code);
//  optype_list__get_opcode__code = optype_list[get_opcode__code];
//  getarg_a__code    = GETARG_A(code);
//  getarg_a__code__a = getarg_a__code + a;
//  optype_list__get_opcode__code = optype_list[get_opcode__code];

    switch(optype_list[GET_OPCODE(code)]) {
//  switch(optype_list__get_opcode__code) {
    case OPTYPE_NONE:
    case OPTYPE_Bx:
    case OPTYPE_sBx:
    case OPTYPE_Ax:
      /* do nothing */
      break;

    case OPTYPE_A:
      code = MKOP_A(GET_OPCODE(code), GETARG_A(code) + a);
//    code = MKOP_A(get_opcode__code, getarg_a__code__a);
      break;

//  default:
//    getarg_b__code	= GETARG_B(code);
//    getarg_b__code__a = getarg_b__code + a;

//    switch(optype_list__get_opcode__code) {
      case OPTYPE_AB:
	code = MKOP_AB(GET_OPCODE(code), GETARG_A(code) + a, GETARG_B(code) + a);
//	code = MKOP_AB(get_opcode__code, getarg_a__code__a, getarg_b__code__a);
	break;

//    default:
///	getarg_b__code	  = GETARG_B(code);
///	getarg_b__code__a = getarg_b__code + a;
//	getarg_c__code	  = GETARG_C(code);
//	getarg_c__code__a = getarg_c__code + a;

//	switch(optype_list__get_opcode__code) {
	case OPTYPE_ABC:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code) + a, GETARG_C(code) + a);
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code__a, getarg_c__code__a);
	  break;

	case OPTYPE_ABsC:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code) + symbase, GETARG_C(code) + a);
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code + symbase, getarg_c__code__a);
	  break;

	case OPTYPE_ABxC:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code), GETARG_C(code) + a);
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code, getarg_c__code__a);
	  break;

	case OPTYPE_ABCx:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code) + a, GETARG_C(code));
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code__a, getarg_c__code);
	  break;


	case OPTYPE_ABxCx:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code), GETARG_C(code));
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code, getarg_c__code);
	  break;

	case OPTYPE_ABsCx:
	  code = MKOP_ABC(GET_OPCODE(code), 
		      GETARG_A(code) + a, GETARG_B(code) + symbase, GETARG_C(code));
//	  code = MKOP_ABC(get_opcode__code, 
//		      getarg_a__code__a, getarg_b__code + symbase, getarg_c__code);
	  break;

///	case OPTYPE_AsBx:
///	    code = MKOP_AsBx(GET_OPCODE(code), GETARG_A(code) + a, GETARG_sBx(code));
///	    code = MKOP_AsBx(get_opcode__code, getarg_a__code__a, GETARG_sBx(code));
///	    break;

///	default:
///	  getarg_bx__code = GETARG_Bx(code);

//	  switch(optype_list__get_opcode__code) {
//	  case OPTYPE_ABx:
	    code = MKOP_ABx(GET_OPCODE(code), GETARG_A(code) + a, GETARG_Bx(code));
//	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, GETARG_Bx(code));
///	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, getarg_bx__code);
	  break;

	  case OPTYPE_ABp:
	    code = MKOP_ABx(GET_OPCODE(code), GETARG_A(code) + a, GETARG_Bx(code) + poolbase);
//	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, GETARG_Bx(code) + poolbase);
///	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, getarg_bx__code + poolbase);
	    break;

	  case OPTYPE_ABs:
	    code = MKOP_ABx(GET_OPCODE(code), GETARG_A(code) + a, GETARG_Bx(code) + symbase);
//	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, GETARG_Bx(code) + symbase);
///	    code = MKOP_ABx(get_opcode__code, getarg_a__code__a, getarg_bx__code + symbase);
	    break;

	  case OPTYPE_AsBx:
	    code = MKOP_AsBx(GET_OPCODE(code), GETARG_A(code) + a, GETARG_sBx(code));
//	    code = MKOP_AsBx(get_opcode__code, getarg_a__code__a, GETARG_sBx(code));
	    break;
//

///	  }
//	}
//    }
    }

    *(curpos++) = code;
  }

  return ent + 2;
}

static mrb_value
mrb_inline_missing(mrb_state *mrb, mrb_value self)
{
  struct RProc *caller_proc;
  struct RProc *callee_proc;
  mrb_irep *caller_irep;
  mrb_irep *callee_irep;
  mrb_value mid;
  mrb_int argc;
  mrb_value *argv;
  mrb_value iml;
  mrb_value pobj;
  int a;
  int i;
//
// mrb_char str__inline_method_list = "__inline_method_list__";	// ? 	// mojiretu

  mrb_get_args(mrb, "o*", &mid, &argv, &argc);
  for (i = 0; i < argc; i++) {
    mrb->c->stack[i + 1] = mrb->c->stack[i + 2];
// for (i = 1; i <= argc; i++) {
//  mrb->c->stack[i] = mrb->c->stack[i + 1];
// for (a = 1; a <= argc; a++) {
//  mrb->c->stack[a] = mrb->c->stack[a + 1];
// i = 1;
// while (i <= argc) {
//  mrb->c->stack[i] = mrb->c->stack[++i];	/* -O0 ? */
//  mrb->c->stack[i++] = mrb->c->stack[i];	/* -O0 ? */
// a = 1;
// while (a <= argc) {
//  mrb->c->stack[a] = mrb->c->stack[++a];	/* -O0 ? */
//  mrb->c->stack[a++] = mrb->c->stack[a];	/* -O0 ? */
  }
  
  caller_proc = mrb->c->ci[-1].proc;
  caller_irep = caller_proc->body.irep;

  iml = mrb_obj_iv_get(mrb, mrb_class(mrb, self), mrb_intern_lit(mrb, "__inline_method_list__"));
// iml = mrb_obj_iv_get(mrb, mrb_class(mrb, self), mrb_intern_lit(mrb, str__inline_method_list));
  if (mrb_nil_p(iml)) {
  iml = mrb_obj_iv_get(mrb, mrb_class_ptr(self), mrb_intern_lit(mrb, "__inline_method_list__"));
// iml = mrb_obj_iv_get(mrb, mrb_class_ptr(self), mrb_intern_lit(mrb, str__inline_method_list));
  }
  
  pobj = mrb_hash_get(mrb, iml, mid);
  /*mrb_p(mrb, iml);
    mrb_p(mrb, mid);*/
  callee_proc = mrb_proc_ptr(pobj);
  callee_irep = callee_proc->body.irep;
  a = mrb->c->ci->acc;
  if (caller_irep->nregs < callee_irep->nregs + a) {
    caller_irep->nregs = callee_irep->nregs + a;
// i = callee_irep->nregs + a;
// if (caller_irep->nregs < i;
//  caller_irep->nregs = i;
  }

  mrb->c->ci->pc =  patch_irep_for_inline(mrb, callee_irep, caller_irep, a);
  mrb->c->ci->target_class = 0;

  return self;
}

static mrb_value
mrb_inline_make_inline_method(mrb_state *mrb, mrb_value self)
{
  struct RObject *obj = mrb_obj_ptr(self);
  mrb_value iml;
  struct RProc *m;
  mrb_value mid;
  struct RClass *c = mrb_class_ptr(self);
// mrb_char str__inline_method_list = "__inline_method_list__";	// ? 	// mojiretu

  mrb_get_args(mrb, "o", &mid);

  iml = mrb_obj_iv_get(mrb, obj, mrb_intern_lit(mrb, "__inline_method_list__"));
// iml = mrb_obj_iv_get(mrb, obj, mrb_intern_lit(mrb, str__inline_method_list));
  if (mrb_nil_p(iml)) {
    iml = mrb_hash_new(mrb);
  }

  m = mrb_method_search_vm(mrb, &c, mrb_symbol(mid));
  if (m == NULL) {
    c = mrb_class(mrb, self);
    m = mrb_method_search_vm(mrb, &c, mrb_symbol(mid));
  }

  mrb_hash_set(mrb, iml, mid, mrb_obj_value(m));
  mrb_obj_iv_set(mrb, obj, mrb_intern_lit(mrb, "__inline_method_list__"), iml);
// mrb_obj_iv_set(mrb, obj, mrb_intern_lit(mrb, str__inline_method_list), iml);
  mrb_undef_method(mrb, c, mrb_sym2name(mrb, mrb_symbol(mid)));

  return self;
}

mrb_value
mrb_inline_included(mrb_state *mrb, mrb_value self)
{
  mrb_value klass;
  struct RClass *clsptr;
  
  mrb_get_args(mrb, "o", &klass);
  clsptr = mrb_class_ptr(klass);
  mrb_define_module_function(mrb, clsptr, "make_inline_method", mrb_inline_make_inline_method, MRB_ARGS_REQ(1));

  return mrb_nil_value();
}

void
mrb_mruby_inline_gem_init(mrb_state *mrb)
{
  struct RClass *inlin;

  inlin = mrb_define_module(mrb, "Inline");
  mrb_define_class_method(mrb, inlin, "included", mrb_inline_included, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, inlin, "method_missing",          mrb_inline_missing,          MRB_ARGS_ANY());
}

void
mrb_mruby_inline_gem_final(mrb_state *mrb)
{
}
