#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"
#include "translate.h"

/*Lab4: Your implementation of lab4*/
#define db 0

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};


struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;
	e.exp = exp;
	e.ty = ty;
	return e;
}

static Ty_fieldList transFieldList(S_table tenv, A_fieldList a); 
static Ty_tyList transTyList(S_table tenv, A_fieldList a);

static struct expty transVar(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_var v);
static struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp a);
static Tr_exp transDec(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_dec d);
static Ty_ty transTy(S_table tenv, A_ty a);

static Ty_ty actual_ty(Ty_ty t); 
static bool cmp_ty(Ty_ty a, Ty_ty b); 

static U_boolList makeFormalList(A_fieldList params);

struct set_ {
	S_symbol s[1000];
	int pos;
};
typedef struct set_ *set;

static set set_init();
static void set_reset(set s);
static bool set_push(set s, S_symbol x);

static set s;

static int loop;


F_fragList SEM_transProg(A_exp exp) {
	assert(exp);
	S_table tenv = E_base_tenv();
	S_table venv = E_base_venv();
	loop = 0;
	s = set_init();
	Tr_init();
	// create main level ? refer to TerCz...why need this...
    Temp_label func_label = Temp_namedlabel("tigermain");
    Tr_level main_level = Tr_newLevel(Tr_outermost(), func_label, NULL);
    E_enventry fun_entry = E_FunEntry(main_level, func_label, NULL, Ty_Void());  // result type is void

	struct expty body_exp =  transExp(main_level, NULL, venv, tenv, exp);

	// find one less than answer
	Tr_procEntryExit(fun_entry->u.fun.level, body_exp.exp, NULL);
	return Tr_getResult();
}

/* 
* 由于之前就没有维护loop栈，遇上break的时候需要找上一个label，
* 接着之前的参考资料，发现是通过函数去维护栈。
*/

struct expty transVar(Tr_level tlevel, Tr_exp texp, S_table venv, S_table tenv, A_var v) {
	switch (v->kind) {
		case A_simpleVar: {
			E_enventry e = S_look(venv, get_simplevar_sym(v));
			if (e && e->kind == E_varEntry) 
				return expTy(Tr_simpleVar(get_var_access(e), tlevel), actual_ty(get_varentry_type(e)));
			else {
				EM_error(v->pos, "undefined variable %s", S_name(get_simplevar_sym(v)));
				return expTy(Tr_null(), Ty_Int());
			}
		}
		case A_fieldVar: {
			struct expty exp = transVar(tlevel, texp, venv, tenv, get_fieldvar_var(v)); 
			Ty_ty t = exp.ty;
			if (t->kind != Ty_record) {
				EM_error(v->pos, "not a record type");
				return expTy(Tr_null(), Ty_Int());
			} else {
				Ty_fieldList fl = t->u.record;
				int i;
				for (fl = t->u.record, i = 0; fl; fl = fl->tail, i++)
					if (fl->head->name == v->u.field.sym) 
						return expTy(Tr_fieldVar(exp.exp, i), actual_ty(fl->head->ty));
				EM_error(v->pos, "field %s doesn't exist", S_name(get_fieldvar_sym(v)));
				return expTy(Tr_null(), Ty_Int());
			}
		}
		case A_subscriptVar: {
			struct expty var = transVar(tlevel, texp, venv, tenv, get_subvar_var(v)); 
			if (var.ty->kind != Ty_array) {
				EM_error(v->pos, "array type required");
			}else{
				struct expty exp = transExp(tlevel, texp, venv, tenv, get_subvar_exp(v));
				if (exp.ty->kind != Ty_int)
					EM_error(v->pos, "Subscript was not an integer");
				else
					return expTy(Tr_subscriptVar(var.exp, exp.exp), actual_ty(get_ty_array(var.ty)));
			}
			return expTy(Tr_null(), actual_ty(get_ty_array(var.ty)));
		}
	}
}

struct expty transExp(Tr_level tlevel, Tr_exp texp, S_table venv, S_table tenv, A_exp a) {
	switch (a->kind) {
		case A_varExp: 
			return transVar(tlevel, texp, venv, tenv, a->u.var);	
		case A_nilExp: 
			return expTy(Tr_null(), Ty_Nil());	
		case A_intExp: 
			return expTy(Tr_intExp(a->u.intt), Ty_Int());	
		case A_stringExp: 
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());	
		case A_callExp: {
			E_enventry fun = S_look(venv, get_callexp_func(a));
			if (!fun) {
				EM_error(a->pos, "undefined function %s", S_name(get_callexp_func(a)));
				return expTy(Tr_null(), Ty_Int());
			} else if (fun->kind == E_varEntry) {
				EM_error(a->pos, "'%s' was a variable", S_name(get_callexp_func(a)));
				return expTy(Tr_null(), fun->u.var.ty);
			}

			Ty_tyList tl = fun->u.fun.formals;
			A_expList el = get_callexp_args(a);
			Tr_expList head = NULL, tail = NULL;
			for (; tl && el; tl = tl->tail, el = el->tail) {
				struct expty exp = transExp(tlevel, texp, venv, tenv, el->head);
				if (!cmp_ty(tl->head, exp.ty))
					EM_error(a->pos, "para type mismatch");

				// add list, check first in
				if (head){
					tail->tail = Tr_ExpList(exp.exp, NULL);
					tail = tail->tail;
				}else {
					head = Tr_ExpList(exp.exp, NULL);
					tail = head;
				}
			}

			// both should be null
			if (tl) 
				EM_error(a->pos, "too few params in function %s", S_name(get_callexp_func(a)));
			else if (el)
				EM_error(a->pos, "too many params in function %s", S_name(get_callexp_func(a)));
			// call type
			#if db
			EM_error(a->pos, "%d", fun->u.fun.result->kind);
			#endif

			return expTy(Tr_callExp(fun->u.fun.label, head, fun->u.fun.level, tlevel), fun->u.fun.result);
		}
		case A_opExp: {
			A_oper oper = get_opexp_oper(a);
			struct expty left = transExp(tlevel, texp, venv, tenv, get_opexp_left(a));
			struct expty right = transExp(tlevel, texp, venv, tenv, get_opexp_right(a));
			switch (oper) {
				case A_plusOp:
				case A_minusOp:
				case A_timesOp:
				case A_divideOp: {
					if (left.ty->kind != Ty_int) 
						EM_error(get_opexp_leftpos(a), "integer required");
					else if (right.ty->kind != Ty_int) 
						EM_error(get_opexp_rightpos(a), "integer required");
					else
						return expTy(Tr_arithExp(get_opexp_oper(a), left.exp, right.exp), Ty_Int());
					return expTy(Tr_null(), Ty_Int());
				}
				case A_eqOp:
				case A_neqOp: {
					Tr_exp exp = Tr_null();
					if (left.ty->kind == Ty_void || right.ty->kind == Ty_void) 
						EM_error(get_opexp_leftpos(a), "expression had no value");	
					else if (!cmp_ty(left.ty, right.ty))
						EM_error(get_opexp_rightpos(a), "same type required");
					// else if (left.ty->kind == Ty_int)
					else if (left.ty->kind == Ty_string)
						exp = Tr_eqStrExp(get_opexp_oper(a), left.exp, right.exp);
					// else if (left.ty->kind == Ty_array)
					// 	exp = Tr_eqRefExp(get_opexp_oper(a), left.exp, right.exp);
					// else if (left.ty->kind == Ty_record)
					// 	exp = Tr_eqRefExp(get_opexp_oper(a), left.exp, right.exp);
					else
						exp = Tr_relExp(get_opexp_oper(a), left.exp, right.exp);
					return expTy(exp, Ty_Int());
				}
				case A_ltOp:
				case A_leOp:
				case A_gtOp:
				case A_geOp: {
					if (left.ty->kind != Ty_int && left.ty->kind != Ty_string) 
						EM_error(get_opexp_leftpos(a), "string or integer required");
					else if (!cmp_ty(left.ty, right.ty))
						EM_error(get_opexp_rightpos(a), "same type required");
					else
						return expTy(Tr_relExp(get_opexp_oper(a), left.exp, right.exp), Ty_Int());
				}
				return expTy(Tr_null(), Ty_Int());
			} 
		} 
		case A_recordExp: {
			Ty_ty t = actual_ty(S_look(tenv, get_recordexp_typ(a)));
			if (!t) {
				EM_error(a->pos, "undefined type %s", S_name(get_recordexp_typ(a)));
				return expTy(Tr_null(), Ty_Int());
			} else if (t->kind != Ty_record) {
				EM_error(a->pos, "'%s' was not a record type", S_name(get_recordexp_typ(a)));
				return expTy(Tr_null(), Ty_Record(NULL));
			}

			Ty_fieldList ti = t->u.record;
			A_efieldList ei = get_recordexp_fields(a);
			// count 
			Tr_expList el = NULL;
			int num = 0;

			// List, head means current..., tail is next...
			for (; ti && ei; ti = ti->tail, ei = ei->tail) {
				if (ti->head->name != ei->head->name) {
					EM_error(a->pos, "need member '%s' but '%s'", S_name(ti->head->name), S_name(ei->head->name));
					continue;
				}
				struct expty exp = transExp(tlevel, texp, venv, tenv, ei->head->exp);
				// head, tail => return {head, tail}
				el = Tr_ExpList(exp.exp, el);
				num++;
				if (!cmp_ty(ti->head->ty, exp.ty))
					EM_error(a->pos, "member '%s' type mismatch", S_name(ti->head->name));
			}

			if (ti) 
				EM_error(a->pos, "too few initializers for '%s'", S_name(get_recordexp_typ(a)));
			else if (ei)
				EM_error(a->pos, "too many initializers for '%s'", S_name(get_recordexp_typ(a)));

			// Tr record, 
			if (num)
				return expTy(Tr_recordExp(num, el), t);
			else
				return expTy(Tr_null(), Ty_Record(NULL));
		}
		// (exp a, exp b, exp c)
		case A_seqExp: {
			if (get_seqexp_seq(a) == NULL)
				return expTy(Tr_null(), Ty_Void());
			A_expList al = get_seqexp_seq(a);
			struct expty et;
			Tr_expList tl = NULL;
			for (; al; al =al->tail) {
				et = transExp(tlevel, texp, venv, tenv, al->head);
				tl = Tr_ExpList(et.exp, tl);	
			}
			return expTy(Tr_seqExp(tl), et.ty);
			// A_expList el = get_seqexp_seq(a);

			// for (; el->tail; el = el->tail){
			// 	transExp(venv, tenv, el->head);
			// }
				
			// return transExp(venv, tenv, el->head);
		}
		case A_assignExp: {
			struct expty var = transVar(tlevel, texp, venv, tenv, get_assexp_var(a));	
			struct expty exp = transExp(tlevel, texp, venv, tenv, get_assexp_exp(a));	
			if (!cmp_ty(var.ty, exp.ty))
				EM_error(a->pos, "unmatched assign exp");
			E_enventry e = S_look(venv, get_assexp_var(a)->u.simple);
            if (e && e->readonly) {
                EM_error(a->pos, "loop variable can't be assigned");
            }
			return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
		}
		case A_ifExp: {
			struct expty t = transExp(tlevel, texp, venv, tenv, get_ifexp_test(a));	
			struct expty h = transExp(tlevel, texp, venv, tenv, get_ifexp_then(a));	
			
			if (t.ty->kind != Ty_int)
				EM_error(a->pos, "if-exp was not an integer");

			// 2016: else is not null
			if (get_ifexp_else(a)) {
				struct expty e = transExp(tlevel, texp, venv, tenv, get_ifexp_else(a));
				if (!cmp_ty(h.ty, e.ty) && !(h.ty->kind == Ty_nil && e.ty->kind == Ty_nil)){
					EM_error(a->pos, "then exp and else exp type mismatch %d %d", h.ty->kind, e.ty->kind);
				}

				#if db
				if (get_ifexp_else(a)->kind == A_nilExp)
					EM_error(a->pos, "then else kind %d %d", h.ty->kind, e.ty->kind);
				// EM_error(a->pos, "then else kind %d %d", h.ty->kind, e.ty->kind);
				#endif

				return expTy(Tr_ifExp(t.exp, h.exp, e.exp), h.ty);
			} else {
				if (h.ty->kind != Ty_void)
					EM_error(a->pos, "if-then exp's body must produce no value");
				return expTy(Tr_ifExp(t.exp, h.exp, NULL), Ty_Void());
			}
		}
		case A_whileExp: {
			struct expty t = transExp(tlevel, texp, venv, tenv, get_whileexp_test(a));	
			Tr_exp done = Tr_doneExp();
			loop++;
			struct expty b = transExp(tlevel, done, venv, tenv, get_whileexp_body(a));	
			loop--;
			if (t.ty->kind != Ty_int)
				EM_error(a->pos, "while-exp was not an integer");
			if (b.ty->kind != Ty_void)
				EM_error(a->pos, "while body must produce no value");
			return expTy(Tr_whileExp(t.exp, b.exp, done), Ty_Void());
		}
		case A_forExp: {
			struct expty l = transExp(tlevel, texp, venv, tenv, get_forexp_lo(a));
			struct expty h = transExp(tlevel, texp, venv, tenv, get_forexp_hi(a));
			if (l.ty->kind != Ty_int || h.ty->kind != Ty_int)
				EM_error(a->pos, "for exp's range type is not integer");
			
			loop++;
			S_beginScope(venv);

			// i variable
			Tr_access iac = Tr_allocLocal(tlevel, a->u.forr.escape);
			E_enventry e = E_ROVarEntry(iac, Ty_Int());
			
			S_enter(venv, get_forexp_var(a), e);
			Tr_exp done = Tr_doneExp();
			struct expty b = transExp(tlevel, done, venv, tenv, get_forexp_body(a));
			
			S_endScope(venv);
			loop--;
			
			if (b.ty->kind != Ty_void)
				EM_error(a->pos, "body exp shouldn't return a value");
			return expTy(Tr_forExp(tlevel, iac, l.exp, h.exp, b.exp, done), Ty_Void());
		}
		case A_breakExp: {
			if (!loop){
				EM_error(a->pos, "break statement not within loop");
				return expTy(Tr_null(), Ty_Void());
			}
			// return to last exp
			else
				return expTy(Tr_breakExp(texp), Ty_Void());
		}
		case A_letExp: {
			struct expty exp;
			A_decList lt;
			S_beginScope(venv);
			S_beginScope(tenv);
			Tr_exp te;
			Tr_expList el = NULL;
			for (lt = get_letexp_decs(a); lt; lt = lt->tail){
				te = transDec(tlevel, texp, venv, tenv, lt->head);
				el = Tr_ExpList(te, el);
			}
			exp = transExp(tlevel, texp, venv, tenv, get_letexp_body(a));
			el = Tr_ExpList(exp.exp, el);
			S_endScope(venv);
			S_endScope(tenv);
			return expTy(Tr_seqExp(el), exp.ty);
		}
		case A_arrayExp: {
			Ty_ty t = actual_ty(S_look(tenv, get_arrayexp_typ(a)));
			if (!t) {
				EM_error(a->pos, "undefined type %s", S_name(get_arrayexp_typ(a)));
				return expTy(Tr_null(), Ty_Int());
			} else if (t->kind != Ty_array) {
				EM_error(a->pos, "'%s' was not a array type", S_name(get_arrayexp_typ(a)));
				return expTy(Tr_null(), Ty_Int());
			}
			struct expty z = transExp(tlevel, texp, venv, tenv, get_arrayexp_size(a));	
			struct expty i = transExp(tlevel, texp, venv, tenv, get_arrayexp_init(a));	
			if (z.ty->kind != Ty_int)
				EM_error(a->pos, "array size was not an integer value");
			if (!cmp_ty(i.ty, t->u.array))
				EM_error(a->pos, "array init type mismatch");
			return expTy(Tr_arrayExp(z.exp, i.exp), t);
		}
	}
}

Tr_exp transDec(Tr_level tlevel, Tr_exp texp, S_table venv, S_table tenv, A_dec d) {
	switch (d->kind) {
		case A_varDec: {
			struct expty e = transExp(tlevel, texp, venv, tenv, d->u.var.init);
			Tr_access ac = Tr_allocLocal(tlevel, d->u.var.escape);
			if (d->u.var.typ) {
				Ty_ty t = S_look(tenv, d->u.var.typ);
				if (!t)
					EM_error(d->pos, "undefined type %s", S_name(d->u.var.typ));
				else {
					if (!cmp_ty(t, e.ty))
						EM_error(d->pos, "var init type mismatch");
					S_enter(venv, d->u.var.var, E_VarEntry(ac, t));
					return Tr_assignExp(Tr_simpleVar(ac, tlevel), e.exp);;
				}
			}
			if (e.ty == Ty_Void())
				EM_error(d->pos, "initialize with no value");
			else if (e.ty == Ty_Nil())
				EM_error(d->pos, "init should not be nil without type specified");
			S_enter(venv, d->u.var.var, E_VarEntry(ac, e.ty));
			return Tr_assignExp(Tr_simpleVar(ac, tlevel), e.exp);
		}

		case A_typeDec: {
			A_nametyList l;
			set_reset(s);
			for (l = d->u.type; l; l = l->tail) {
				if (!set_push(s, l->head->name)) {
					EM_error(d->pos, "two types have the same name", S_name(l->head->name));
					continue;
				}
				Ty_ty t = Ty_Name(l->head->name, NULL);
				S_enter(tenv, l->head->name, t);
			}

			set_reset(s);
			for (l = d->u.type; l; l = l->tail) {
				if (!set_push(s, l->head->name)) 
					continue;
				Ty_ty t = S_look(tenv, l->head->name);
				t->u.name.ty = transTy(tenv, l->head->ty);
			}

			// recursive definition
			for (l = d->u.type; l; l = l->tail) {
				Ty_ty t = S_look(tenv, l->head->name);
				set_reset(s);
				t = t->u.name.ty;
				while (t && t->kind == Ty_name) {
					if (!set_push(s, t->u.name.sym)) {
						EM_error(d->pos, "illegal type cycle");
						t->u.name.ty = Ty_Int();
						break;
					}
					t = t->u.name.ty;
				}
			}
			return Tr_null();
		}
		case A_functionDec: {
			A_fundecList fl;
			set fs = set_init();
			set_reset(fs);
			for (fl = d->u.function; fl; fl = fl->tail) {
				A_fundec fun = fl->head;
				if (!set_push(fs, fun->name)) {
					EM_error(fun->pos, "two functions have the same name", S_name(fun->name));
					continue;
				}
				Ty_ty re = NULL;
				// get result type
				if (fun->result) {
					re = S_look(tenv, fun->result);
					if (!re) {
						EM_error(d->pos, "function result: undefined type %s", S_name(fun->result));
						re = Ty_Int();
					}
				} else
					re = Ty_Void();
				set_reset(s);
				Ty_tyList pa = transTyList(tenv, fun->params);
				Temp_label la = Temp_newlabel();

				// function => new level
				Tr_level le = Tr_newLevel(tlevel, la, makeFormalList(fun->params));

				// funentry + level and Temp label
				S_enter(venv, fun->name, E_FunEntry(le, la, pa, re));
			}

			set_reset(fs);
			for (fl = d->u.function; fl; fl = fl->tail) {
				A_fundec fun = fl->head;
				if (!set_push(fs, fun->name))
					continue;
				E_enventry ent = S_look(venv, fun->name);
				S_beginScope(venv);
				A_fieldList el = fun->params;
				// access update, skip link
				Tr_accessList al = Tr_formals(ent->u.fun.level)->tail;
				set_reset(s);
				int elc = 0;
				for (el = fun->params; el; el = el->tail) {
					fprintf(stderr, "el :%d\n", elc++);
					if (!set_push(s, el->head->name))
						continue;
					Ty_ty t = S_look(tenv, el->head->typ);
					if (!t)
						t = Ty_Int();
					S_enter(venv, el->head->name, E_VarEntry(al->head, t));
					al = al->tail;
				}
				
				struct expty exp = transExp(ent->u.fun.level, texp, venv, tenv, fun->body);
				Tr_procEntryExit(ent->u.fun.level, exp.exp, al);

				if (ent->u.fun.result->kind == Ty_void && exp.ty->kind != Ty_void)
					EM_error(fun->pos, "procedure returns value", S_name(fun->name));
				else if (!cmp_ty(ent->u.fun.result, exp.ty))
					EM_error(fun->pos, "body result type mismatch");
				S_endScope(venv);
			}
			return Tr_null();
		}
	}
}

Ty_ty transTy(S_table tenv, A_ty a) {
	switch (a->kind) {
		case A_nameTy: {
			Ty_ty t = S_look(tenv, get_ty_name(a));
			if (!t) {
				EM_error(a->pos, "undefined type %s", S_name(get_ty_name(a)));
				return Ty_Int();
			} else
				return Ty_Name(get_ty_name(a), t);
		}
		case A_recordTy:
			set_reset(s);
			return Ty_Record(transFieldList(tenv, get_ty_record(a)));
		case A_arrayTy: {
			Ty_ty t = S_look(tenv, get_ty_array(a));
			if (!t) {
				EM_error(a->pos, "undefined type %s", S_name(get_ty_array(a)));
				return Ty_Array(Ty_Int());
			} else
				return Ty_Array(S_look(tenv, get_ty_array(a)));
		}
	}
	
}


Ty_fieldList transFieldList(S_table tenv, A_fieldList a) {
	if (!a)
		return NULL;
	if (!set_push(s, a->head->name)) {
		EM_error(a->head->pos, "redeclaration of '%s'", S_name(a->head->name));
		return transFieldList(tenv, a->tail);
	}
	Ty_ty t = S_look(tenv, a->head->typ);
	if (!t) {
		EM_error(a->head->pos, "undefined type %s", S_name(a->head->typ));
		t = Ty_Int();
	}
	return Ty_FieldList(Ty_Field(a->head->name, t), transFieldList(tenv, a->tail));
}

Ty_tyList transTyList(S_table tenv, A_fieldList a) {
	if (!a)
		return NULL;
	if (!set_push(s, a->head->name)) {
		EM_error(a->head->pos, "redeclaration of '%s'", S_name(a->head->name));
		return transTyList(tenv, a->tail);
	}
	Ty_ty t = S_look(tenv, a->head->typ);
	if (!t) {
		EM_error(a->head->pos, "undefined type %s", S_name(a->head->typ));
		t = Ty_Int();
	}
	return Ty_TyList(t, transTyList(tenv, a->tail));
}

bool cmp_ty(Ty_ty a, Ty_ty b) {
	assert(a&&b);
	a = actual_ty(a);
	b = actual_ty(b);
	if (a == b)
		return TRUE;
	else {
		if (a->kind == Ty_record && b->kind == Ty_nil || a->kind == Ty_nil && b->kind == Ty_record)
			return TRUE;
		else 
			return FALSE;
	}
}

U_boolList makeFormalList(A_fieldList params) {
	U_boolList head = NULL, tail = NULL;
	while (params) {
		if (head) {
			tail->tail = U_BoolList(params->head->escape, NULL);
			tail = tail->tail;
		} else {
			head = U_BoolList(params->head->escape, NULL);
			tail = head;
		}
		params = params->tail;
	}
	return head;
}

Ty_ty actual_ty(Ty_ty t) {
	if (!t)
		return NULL;
	while (t && t->kind == Ty_name)
		t = t->u.name.ty;
	return t;
}

set set_init() {
	set t = checked_malloc(sizeof(*t));
	t->pos = 0;
	return t;
}

void set_reset(set s) {
	s->pos = 0;
}

bool set_push(set s, S_symbol x) {
	int i;
	for (i = 0; i < s->pos; i++)
		if (s->s[i] == x)
			return FALSE;
	s->s[s->pos++] = x;
	return TRUE;
}
