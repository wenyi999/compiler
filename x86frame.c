#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/


static F_access InFrame(int offset);
static F_access InReg(Temp_temp reg);

const int F_wordSize = 8;		//x86-64: 64bit
static const int F_keep = 6;	//number of parameters kept in regs;

/* function implementation */
F_accessList F_AccessList(F_access head, F_accessList tail) {
	F_accessList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
	F_frame fr = checked_malloc(sizeof(*fr));
	fr->label = name;		
	fr->formals = NULL;
	fr->locals = NULL;
	fr->local_count = 0;

	F_accessList head = NULL, tail = NULL;

	// register count
	int rn = 0, fn = 0;
	U_boolList ptr;
	for (ptr = formals; ptr; ptr = ptr->tail) {
		fprintf(stderr, "rn :%d ptr\n", rn);
		F_access ac = NULL;
		// head->current, bool escape
		if (rn < F_keep) {
			if (ptr->head){
				fprintf(stderr, "rn :%d escape\n", rn);
				fr->local_count++;
				ac = InFrame(-(fr->local_count)*F_wordSize);
			}else
				ac = InReg(Temp_newtemp());
			rn++;
		} else {
			ac = InFrame((fn++)*F_wordSize);
		}

		if (head) {
			tail->tail = F_AccessList(ac, NULL);
			tail = tail->tail;
		} else {
			head = F_AccessList(ac, NULL);
			tail = head;
		}
	}
	fprintf(stderr, "rn end\n");
	fr->formals = head;

	return fr;
}

// encapsulation
Temp_label F_name(F_frame f) {
	return f->label;
}

F_accessList F_formals(F_frame f) {
	return f->formals;
}

static int db = 0;
F_access F_allocLocal(F_frame f, bool escape) {
	fprintf(stderr, "alloc :%d %d\n", db++, escape);
	if (escape) {
		f->local_count++;
		return InFrame(-F_wordSize * (f->local_count));
	}
	else 
		return InReg(Temp_newtemp());
}

// when the acc is from an inner-nested function, it's calculated by static link
T_exp F_Exp(F_access acc, T_exp framePtr) {
	if (acc->kind == inReg)
		return T_Temp(acc->u.reg);
	else
		return T_Mem(T_Binop(T_plus, T_Const(acc->u.offset), framePtr));
}

// ???
T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}

// constructor
static F_access InFrame(int offset) {
	F_access ac = checked_malloc(sizeof(*ac));
	ac->kind = inFrame;
	ac->u.offset = offset;
	return ac;
}

static F_access InReg(Temp_temp reg) {
	F_access ac = checked_malloc(sizeof(*ac));
	ac->kind = inReg;
	ac->u.reg = reg;
	return ac;
}

/* fragment */

// S_symbol is a pointer
F_frag F_StringFrag(Temp_label label, string str) {
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_stringFrag;
	frag->u.stringg.label = label;
	frag->u.stringg.str = str;
	return frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_procFrag;
	frag->u.proc.body = body;
	frag->u.proc.frame = frame;
	return frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
	F_fragList fl = checked_malloc(sizeof(*fl));
	fl->head = head;
	fl->tail = tail;
	return fl;
}                                             


#define regdec  {static Temp_temp t = NULL;if (!t)t = Temp_newtemp();return t;}

Temp_temp F_FP() regdec

Temp_temp F_RAX(void) regdec
Temp_temp F_RBX(void) regdec
Temp_temp F_RCX(void) regdec
Temp_temp F_RDX(void) regdec
Temp_temp F_RSI(void) regdec
Temp_temp F_RDI(void) regdec
Temp_temp F_RBP(void) regdec
Temp_temp F_RSP(void) regdec
Temp_temp F_R8(void) regdec
Temp_temp F_R9(void) regdec
Temp_temp F_R10(void) regdec
Temp_temp F_R11(void) regdec
Temp_temp F_R12(void) regdec
Temp_temp F_R13(void) regdec
Temp_temp F_R14(void) regdec
Temp_temp F_R15(void) regdec