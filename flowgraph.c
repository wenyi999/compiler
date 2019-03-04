#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
	AS_instr inst = (AS_instr) G_nodeInfo(n);
    if (inst->kind == I_OPER)
        return inst->u.OPER.dst;
    else if (inst->kind == I_MOVE)
        return inst->u.MOVE.dst;
    else
        return NULL;
}

Temp_tempList FG_use(G_node n) {
	AS_instr inst = (AS_instr) G_nodeInfo(n);
    if (inst->kind == I_OPER)
        return inst->u.OPER.src;
    else if (inst->kind == I_MOVE)
        return inst->u.MOVE.src;
    else
        return NULL;
}

bool FG_isMove(G_node n) {
	AS_instr inst = (AS_instr) G_nodeInfo(n);
    return inst->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
    G_graph g = G_Graph();
    G_node prev = NULL;

    TAB_table label_table = TAB_empty();
    AS_instrList cur;
    for (cur = il;cur;cur=cur->tail){
        G_node n = G_Node(g, cur->head);
        if (prev) G_addEdge(prev, n);
        if (cur->head->kind == I_OPER && !strncmp("jmp", cur->head->u.OPER.assem, 3))
            prev = NULL;
        else
            prev = n;
        if (cur->head->kind == I_LABEL)
            TAB_enter(label_table, cur->head->u.LABEL.label, n);
    }
  
    // link jmp->label
    G_nodeList nodes = G_nodes(g);
    for (;nodes;nodes=nodes->tail){
        G_node n = nodes->head;
        AS_instr inst = (AS_instr) G_nodeInfo(n);
        Temp_labelList targets = NULL;
        if (inst->kind == I_OPER && inst->u.OPER.jumps != NULL)
            targets = inst->u.OPER.jumps->labels;

        for(;targets;targets=targets->tail){
            G_node tn = TAB_look(label_table, targets->head);
            if (tn) G_addEdge(n, tn);
        }
    }

	return g;
}
