
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"


typedef struct F_access_ *F_access;

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

typedef struct F_accessList_ *F_accessList;

// the frame->access->head is static link, tail -> others
struct F_accessList_ {F_access head; F_accessList tail;};

/* temp */
F_accessList F_AccessList(F_access head, F_accessList tail);

typedef struct F_frame_ *F_frame;

struct F_frame_ {
	F_accessList formals, locals;
	int local_count;
	Temp_label label;
};

extern const int F_wordSize;

F_frame F_newFrame(Temp_label name, U_boolList formals);

Temp_label F_name(F_frame f);
F_accessList F_formals(F_frame f);
F_access F_allocLocal(F_frame f, bool escape);

T_exp F_Exp(F_access acc, T_exp framePtr);

T_exp F_externalCall(string s, T_expList args);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);

T_stm F_procEntryExit1(F_frame frame, T_stm stm); // TODO

Temp_temp F_FP(void);

Temp_temp F_RAX(void);
Temp_temp F_RBX(void);
Temp_temp F_RCX(void);
Temp_temp F_RDX(void);
Temp_temp F_RSI(void);
Temp_temp F_RDI(void);
Temp_temp F_RBP(void);
Temp_temp F_RSP(void);
Temp_temp F_R8(void);
Temp_temp F_R9(void);
Temp_temp F_R10(void);
Temp_temp F_R11(void);
Temp_temp F_R12(void);
Temp_temp F_R13(void);
Temp_temp F_R14(void);
Temp_temp F_R15(void);

#endif
