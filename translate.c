#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"


static Tr_level outer = NULL;
extern const int F_wordSize;

//LAB5: you can modify anything you want.



/*
* assert用在参数为指针的函数中，为了让程序宕在出错的地方，并且提供信息
* assert用在default分支，发现未被处理的地方
*/

/**************/
struct Tr_access_ {
	Tr_level level;
	F_access access;
};


struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
	Temp_label name;
	Tr_accessList formals;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};



/** function **/

static Tr_access Tr_Access(Tr_level level, F_access access);
static Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);
static Tr_accessList makeFormalList(Tr_level l);   //trans F_accessList to Tr_accessList


static patchList PatchList(Temp_label *head, patchList tail);
static patchList doPatch(patchList tList, Temp_label label);
static patchList joinPatch(patchList first, patchList second);

static Tr_exp Tr_Ex(T_exp ex);
static Tr_exp Tr_Nx(T_stm nx);
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm);

static T_exp unEx(Tr_exp e);
static T_stm unNx(Tr_exp e);
static struct Cx unCx(Tr_exp e);

static T_exp trackLink(Tr_level l, Tr_level g);		//track static link from l to g
static T_expList Tr_transExpList(Tr_expList l);

/******* frame *******/

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
	Tr_expList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

// init the level
Tr_level Tr_outermost(void) {
	if (!outer)
		outer = Tr_newLevel(NULL, Temp_newlabel(), NULL);
	return outer;
}

// level变化就意味着有新的函数，所以也需要栈。
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
	Tr_level l = checked_malloc(sizeof(*l));
	l->parent = parent;
	l->name = name;
	l->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	l->formals = makeFormalList(l);
	return l;
}

Tr_accessList Tr_formals(Tr_level level) {
  return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) {
	return Tr_Access(level, F_allocLocal(level->frame, escape));
}


/******* ir tree *******/

static F_fragList fragList;
static F_fragList frag_tail;

F_fragList Tr_getResult() {
	return fragList->tail;
}

static void Tr_addFrag(frag){
	frag_tail->tail = F_FragList(frag, NULL);
	frag_tail = frag_tail->tail;
}

void Tr_init(){
	fragList = F_FragList(NULL, NULL);
	frag_tail = fragList;
}
void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) {
	F_frag frag = F_ProcFrag(T_Move(T_Temp(F_RAX()), unEx(body)), level->frame);
	Tr_addFrag(frag);
	// fragList = F_FragList(frag, fragList);
}

Tr_exp Tr_null() {
	return Tr_Ex(T_Const(0));
}

// trackLink find the right level
Tr_exp Tr_simpleVar(Tr_access acc, Tr_level lev) {
	assert(acc && lev);
	return Tr_Ex(F_Exp(acc->access, trackLink(lev, acc->level)));
}

// compare field to name by semant, then found the off
Tr_exp Tr_fieldVar(Tr_exp base, int off) {
	assert(base);
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Const(off * F_wordSize))));
}

// index's type is Tr_exp, because it can be a expression
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index) {
	assert(base && index);
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Binop(
						T_mul, unEx(index), T_Const(F_wordSize)))));
}


Tr_exp Tr_intExp(int val) {
	return Tr_Ex(T_Const(val));
}

// u.name => temp_label
Tr_exp Tr_stringExp(string str) {
	Temp_label lb = Temp_newlabel();
	F_frag frag = F_StringFrag(lb, str);
	Tr_addFrag(frag);
	return Tr_Ex(T_Name(lb));
}


Tr_exp Tr_callExp(Temp_label fun, Tr_expList el, Tr_level caller, Tr_level callee) {
	assert(fun);
	T_exp ex;
	T_expList args = Tr_transExpList(el);

	if (caller->parent) {
		ex = T_Call(T_Name(fun), 
		T_ExpList(trackLink(callee, caller->parent), args));
	} else {
		// assert(0);
		ex = F_externalCall(Temp_labelstring(fun), args);
	}	
	
	// static link
	// args = T_ExpList(trackLink(callee, caller->parent), args);
	return Tr_Ex(ex);	
}


Tr_exp Tr_arithExp(A_oper oper, Tr_exp left, Tr_exp right) {
	assert(left && right);
	T_binOp op;
	switch (oper) {
		case A_plusOp:		op = T_plus; break;
		case A_minusOp:		op = T_minus; break;
		case A_timesOp:		op = T_mul;	break;
		case A_divideOp:	op = T_div; break;
		default:	assert(0);
	}
	return Tr_Ex(T_Binop(op, unEx(left), unEx(right)));	
}


// condition
Tr_exp Tr_relExp(A_oper oper, Tr_exp left, Tr_exp right) {
	assert(left && right);
	T_relOp op;
	switch (oper) {
		case A_eqOp:	op = T_eq;	break;
		case A_neqOp:	op = T_ne;	break;
		case A_ltOp:	op = T_lt;	break;
		case A_leOp:	op = T_le;	break;
		case A_gtOp:	op = T_gt;	break;
		case A_geOp:	op = T_ge;	break;
		default:	assert(0);
	}
	T_stm stm = T_Cjump(op, unEx(left), unEx(right), NULL, NULL);

	// & get the address, Cx fill.
	patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
	patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
	return Tr_Cx(trues, falses, stm);
}

Tr_exp Tr_eqStrExp(A_oper oper, Tr_exp left, Tr_exp right) {
	// function name: stringEqual ?
	T_exp ans = F_externalCall(String("stringEqual"), 
								T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
	if (oper == A_eqOp)
		return Tr_Ex(ans);
	else
		return Tr_Ex(T_Binop(T_minus, T_Const(1), ans));	
}

Tr_exp Tr_recordExp(int n, Tr_expList l) {
	assert(n && l);
	Temp_temp r = Temp_newtemp();
	T_stm alloc = T_Move(T_Temp(r), F_externalCall(String("malloc"), T_ExpList(T_Const(n*F_wordSize), NULL)));
	int i = n - 1;
	T_stm seq = T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i-- * F_wordSize))),  unEx(l->head));

	for (l = l->tail; l; l = l->tail, i--) {
		seq = T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i*F_wordSize))),  unEx(l->head)), seq); 
	}
	return Tr_Ex(T_Eseq(T_Seq(alloc, seq), T_Temp(r)));
}

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init) {
	assert(size && init);
	return Tr_Ex(F_externalCall(String("initArray"), 
								 T_ExpList(unEx(size), 
								 T_ExpList(unEx(init), NULL))));
}

// ESEQ
Tr_exp Tr_seqExp(Tr_expList l) {
	assert(l);	
	T_exp seq = unEx(l->head);
	Tr_expList ptr;
	for (ptr = l->tail; ptr; ptr = ptr->tail) 
		seq = T_Eseq(unNx(ptr->head), seq);
	return Tr_Ex(seq);
}

Tr_exp Tr_assignExp(Tr_exp left, Tr_exp right) {
	return Tr_Nx(T_Move(unEx(left), unEx(right)));
}

Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee) {
	assert(test && then);
	struct Cx cond = unCx(test);
	Temp_label t = Temp_newlabel();
	Temp_label f = Temp_newlabel();
	doPatch(cond.trues, t);
	doPatch(cond.falses, f);

	// here assume NULL
	if (!elsee) 
	{	
		//if - then
		return Tr_Nx(T_Seq(cond.stm, 
				T_Seq(T_Label(t),
				  T_Seq(unNx(then),
					T_Label(f)))));
	} else {
		//if - then - else
		Temp_label join = Temp_newlabel();
		T_stm joinJump = T_Jump(T_Name(join), Temp_LabelList(join, NULL));
	
		// no result
		if (then->kind == Tr_nx || elsee->kind == Tr_nx) { 
			return Tr_Nx(T_Seq(cond.stm,
						  T_Seq(T_Label(t),
						   T_Seq(unNx(then),
						    T_Seq(joinJump,
							 T_Seq(T_Label(f),
							  T_Seq(unNx(elsee),
									T_Label(join))))))));
		} else {
			//todo:  special treatment for cx
			// if (then->kind == Tr_cx)
			Temp_temp r = Temp_newtemp();
			//Eseq(a,b), b is evaluated as result
			return Tr_Ex(T_Eseq(cond.stm, 
						  T_Eseq(T_Label(t),
						   T_Eseq(T_Move(T_Temp(r), unEx(then)),
						    T_Eseq(joinJump,
							 T_Eseq(T_Label(f),
							  T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
							   T_Eseq(T_Label(join), 
									  T_Temp(r)))))))));
									
		}
	}
}

/* 
* why use Tr_exp done to represent the jump label?
* we place frame and temp under translate
* so we shouldn't use temp in semant
* Unfortunately, Tr_exp is confusing...
*/

Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Tr_exp done) {
	assert(test);
	assert(body);
	struct Cx cond = unCx(test);
	Temp_label lbTest = Temp_newlabel();
	Temp_label lbBody = Temp_newlabel();
	Temp_label lbDone = unEx(done)->u.NAME;
	doPatch(cond.trues, lbBody);
	doPatch(cond.falses, lbDone);

	// here cond.stm produce "goto next line", it's not necessary
	// the problem is we just need if xx goto but Cx is if xx goto 1 else goto 2.
	return Tr_Nx(T_Seq(T_Label(lbTest),
				  T_Seq(cond.stm,
				   T_Seq(T_Label(lbBody),
					T_Seq(unNx(body),
					 T_Seq(T_Jump(T_Name(lbTest), Temp_LabelList(lbTest, NULL)),
						   T_Label(lbDone)))))));
}

// done is the same as while
// if i and limit are locals ??? it seems right...
Tr_exp Tr_forExp(Tr_level lev, Tr_access iac, Tr_exp lo, Tr_exp hi, Tr_exp body, Tr_exp done) {
	
	// let
	Tr_exp ex_i = Tr_simpleVar(iac, lev);
	T_stm istm = unNx(Tr_assignExp(ex_i, lo));
	Tr_access limac = Tr_allocLocal(lev, FALSE);
	Tr_exp ex_lim = Tr_simpleVar(limac, lev);
	T_stm limstm = unNx(Tr_assignExp(ex_lim, hi));

	// in while l <= limit
	T_stm whstm = T_Cjump(T_le, unEx(ex_i), unEx(ex_lim), NULL, NULL);
	patchList trues = PatchList(&whstm->u.CJUMP.true, NULL);
	patchList falses = PatchList(&whstm->u.CJUMP.false, NULL);
	struct Cx whcond = unCx(Tr_Cx(trues, falses, whstm));

	Temp_label lbTest = Temp_newlabel();
	Temp_label lbBody = Temp_newlabel();
	Temp_label lbDone = unEx(done)->u.NAME;

	doPatch(whcond.trues, lbBody);
	doPatch(whcond.falses, lbDone);

	// do body
	T_stm dobody = T_Seq(unNx(body), 
						  T_Move(unEx(ex_i), 
								 T_Binop(T_plus, unEx(ex_i), T_Const(1))));

	// as "while", goto lbBody is redundant
	T_stm circle = T_Seq(T_Label(lbTest),
					 T_Seq(whcond.stm,
					   T_Seq(T_Label(lbBody),
						T_Seq(dobody,
					  	  T_Seq(T_Jump(T_Name(lbTest), Temp_LabelList(lbTest, NULL)),
						    T_Label(lbDone))))));

	return Tr_Nx(T_Seq(T_Seq(istm, limstm), circle));
}

Tr_exp Tr_doneExp() {
	return Tr_Ex(T_Name(Temp_newlabel()));
}

// jump to last done
Tr_exp Tr_breakExp(Tr_exp done) {
	assert(done);
	Temp_label lbDone = unEx(done)->u.NAME;
	return Tr_Nx(T_Jump(unEx(done), Temp_LabelList(lbDone, NULL)));
}

static Tr_access Tr_Access(Tr_level level, F_access access) {
	Tr_access a = checked_malloc(sizeof(*a));
	a->level = level;
	a->access = access;
	return a;
}

static Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail) {
	Tr_accessList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l; 
}

static patchList PatchList(Temp_label *head, patchList tail) {
	patchList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

static patchList doPatch(patchList tList, Temp_label label) {
	for (; tList; tList = tList->tail)
		*(tList->head) = label;
}

static patchList joinPatch(patchList first, patchList second) {
	if (!first)	
		return second;
	for (; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

static Tr_exp Tr_Ex(T_exp ex) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_ex;
	e->u.ex = ex;
	return e;
}

static Tr_exp Tr_Nx(T_stm nx) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_nx;
	e->u.nx = nx;
	return e;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
	Tr_exp e = checked_malloc(sizeof(*e));
	e->kind = Tr_cx;
	e->u.cx.trues = trues;
	e->u.cx.falses = falses;
	e->u.cx.stm = stm;
	return e;
}

// expression
static T_exp unEx(Tr_exp e) {
	assert(e);
	switch (e->kind) {
		case Tr_ex:
			return e->u.ex;
		case Tr_nx:
			return T_Eseq(e->u.nx, T_Const(0));
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel();
			Temp_label f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					T_Eseq(e->u.cx.stm,
					 T_Eseq(T_Label(f),
					  T_Eseq(T_Move(T_Temp(r), T_Const(0)),
					   T_Eseq(T_Label(t),
						   T_Temp(r))))));
		}
	}
	assert(0);
}

// no result
static T_stm unNx(Tr_exp e) {
	assert(e);
	switch (e->kind) { 
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx: {
			Temp_label label = Temp_newlabel();
            doPatch(e->u.cx.trues, label);
            doPatch(e->u.cx.falses, label);
            return T_Seq(e->u.cx.stm, T_Label(label));
		}
	}
	assert(0);
}

static struct Cx unCx(Tr_exp e) {
	assert(e);
	switch (e->kind) {
		case Tr_ex: {
			//todo:   special const(1) const(0)
			T_stm s = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
			patchList t = PatchList(&(s->u.CJUMP.true), NULL);
			patchList f = PatchList(&(s->u.CJUMP.false), NULL);
			Tr_exp tmp = Tr_Cx(t, f, s);
			return tmp->u.cx;
		}
		case Tr_cx:
			return e->u.cx;
	}
	assert(0);
}


static Tr_accessList makeFormalList(Tr_level l) {
	Tr_accessList head = NULL, tail = NULL;
	F_accessList ptr = F_formals(l->frame);
	for (; ptr; ptr = ptr->tail) {
		Tr_access ac = Tr_Access(l, ptr->head);
		if (head) {
			tail->tail = Tr_AccessList(ac, NULL);
			tail = tail->tail;
		} else {
			head = Tr_AccessList(ac, NULL);
			tail = head;
		}
	}
	return head;
}

static T_exp trackLink(Tr_level callee, Tr_level target) {
	T_exp e = T_Temp(F_FP());
	while (callee && callee != target) {
		assert(callee);
		// head->static link
		F_access ac = F_formals(callee->frame)->head;
		e = F_Exp(ac, e);
		callee = callee->parent;
	}
	return e;
}

static T_expList Tr_transExpList(Tr_expList l) {
	T_expList h = NULL, t = NULL;
	for (; l; l = l->tail) {
		if (h) {
			t->tail = T_ExpList(unEx(l->head), NULL);
			t = t->tail;
		} else {
			h = T_ExpList(unEx(l->head), NULL);
			t = h;
		}
	}
	return h;
}

