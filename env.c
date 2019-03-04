#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h" 

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Tr_access access, Ty_ty ty) {
	E_enventry e = checked_malloc(sizeof(*e));
	e->kind = E_varEntry;
	e->u.var.access = access;
	e->u.var.ty = ty;
	return e;
}

E_enventry E_ROVarEntry(Tr_access access, Ty_ty ty) {
    E_enventry e = checked_malloc(sizeof(*e));

    e->kind = E_varEntry;
    e->u.var.access = access;
    e->u.var.ty = ty;
    e->readonly = 1;
    return e;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result) {
	E_enventry e = checked_malloc(sizeof(*e));
	e->kind = E_funEntry;
	e->u.fun.level = level;
	e->u.fun.label = label;
	e->u.fun.formals = formals;
	e->u.fun.result = result;
	return e;
}

S_table E_base_tenv() {
	S_table t = S_empty();
	S_enter(t, S_Symbol("int"), Ty_Int());
	S_enter(t, S_Symbol("string"), Ty_String());
	return t;
}

S_table E_base_venv() {
	S_table t = S_empty();
	S_enter(t, S_Symbol("print"), E_FunEntry(Tr_outermost(), Temp_namedlabel("print"), Ty_TyList(Ty_String(), NULL), Ty_Void()));
	S_enter(t, S_Symbol("flush"), E_FunEntry(Tr_outermost(), Temp_namedlabel("flush"), NULL, Ty_Void()));
	S_enter(t, S_Symbol("getchar"), E_FunEntry(Tr_outermost(), Temp_namedlabel("getchar"), NULL, Ty_String()));
	S_enter(t, S_Symbol("ord"), E_FunEntry(Tr_outermost(), Temp_namedlabel("ord"), Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(t, S_Symbol("chr"), E_FunEntry(Tr_outermost(), Temp_namedlabel("chr"), Ty_TyList(Ty_Int(), NULL), Ty_String()));
	S_enter(t, S_Symbol("size"), E_FunEntry(Tr_outermost(), Temp_namedlabel("size"), Ty_TyList(Ty_String(), NULL), Ty_Int()));
	S_enter(t, S_Symbol("substring"), E_FunEntry(Tr_outermost(), Temp_namedlabel("substring"), Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(), Ty_TyList(Ty_Int(), NULL))), Ty_String()));
	S_enter(t, S_Symbol("concat"), E_FunEntry(Tr_outermost(), Temp_namedlabel("concat"), Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
	S_enter(t, S_Symbol("not"), E_FunEntry(Tr_outermost(), Temp_namedlabel("not"), Ty_TyList(Ty_Int(), NULL), Ty_Int()));
	S_enter(t, S_Symbol("exit"), E_FunEntry(Tr_outermost(), Temp_namedlabel("exit"), Ty_TyList(Ty_Int(), NULL), Ty_Void()));
	S_enter(t, S_Symbol("printi"), E_FunEntry(Tr_outermost(), Temp_namedlabel("printi"), Ty_TyList(Ty_Int(), NULL), Ty_Void()));
	return t;
}
