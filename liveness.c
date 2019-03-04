#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

static G_node tempToNode(TAB_table tb, Temp_temp t, G_graph g);
static bool dfs_live(G_nodeList nodes);
static bool loop_live(G_nodeList nodes);
static Temp_tempList unionTempList(Temp_tempList a, Temp_tempList b);
static Temp_tempList subTempList(Temp_tempList a, Temp_tempList b);
static bool isEqual(Temp_tempList a, Temp_tempList b);
static bool inTempList(Temp_tempList a, Temp_temp t);

static bool inMoveList(Live_moveList a, G_node src, G_node dst);

static G_table inTab, outTab;

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}


Temp_temp Live_gtemp(G_node n) {
	return G_nodeInfo(n);
}

struct Live_graph Live_liveness(G_graph flow) {
	struct Live_graph lg;

	// a good idea from Jzy, G_table acts as std::map 
	inTab = G_empty();
	outTab = G_empty();
	G_nodeList nodes;
	for (nodes = G_nodes(flow); nodes; nodes = nodes->tail) {
		G_enter(inTab, nodes->head, checked_malloc(sizeof(Temp_tempList)));
		G_enter(outTab, nodes->head, checked_malloc(sizeof(Temp_tempList)));
	}

	while(dfs_live(G_nodes(flow)));
	
	TAB_table temp_to_node = TAB_empty();
	lg.graph = G_Graph();
	lg.moves = NULL;
	/* enter hard registers and addEdge */
	Temp_tempList hardRegs = 
			Temp_TempList(F_RAX(),
			Temp_TempList(F_RBX(),
			Temp_TempList(F_RCX(),
			Temp_TempList(F_RDX(),
			Temp_TempList(F_RDI(),
			Temp_TempList(F_RSI(),
			Temp_TempList(F_RBP(),
			Temp_TempList(F_R8(),
			Temp_TempList(F_R9(),
			Temp_TempList(F_R10(),
			Temp_TempList(F_R11(),
			Temp_TempList(F_R12(),
			Temp_TempList(F_R13(),
			Temp_TempList(F_R14(),
			Temp_TempList(F_R15(),
			Temp_TempList(F_RSP(), NULL))))))))))))))));
	Temp_tempList temps;
	for (temps = hardRegs; temps; temps = temps->tail) {
		G_node tempNode = G_Node(lg.graph, temps->head);
		TAB_enter(temp_to_node, temps->head, tempNode);
	}

	for (temps = hardRegs; temps; temps = temps->tail) {
		Temp_tempList next;
		for (next = temps->tail; next; next = next->tail) {
			G_node a = TAB_look(temp_to_node, temps->head);
			G_node b = TAB_look(temp_to_node, next->head);
			G_addEdge(a, b);
			G_addEdge(b, a);
		}
	}

	// add conflict edge
	for (nodes = G_nodes(flow); nodes; nodes = nodes->tail) {
		G_node n = nodes->head;
		Temp_tempList def;
		for (def = FG_def(n); def; def = def->tail) {
				
			G_node a = tempToNode(temp_to_node, def->head, lg.graph);
			Temp_tempList out;
			for (out = *(Temp_tempList *)G_look(outTab, n); out; out = out->tail) {
				if (out->head == def->head) 
					continue;
				
				G_node b = tempToNode(temp_to_node, out->head, lg.graph);

				if (!G_inNodeList(a, G_adj(b)) && (!FG_isMove(n) || !inTempList(FG_use(n), out->head))) {
					G_addEdge(a, b);
					G_addEdge(b, a);
				}
			}

			// add movelist
			if (!FG_isMove(n))
				continue;

			for (out = FG_use(n); out; out = out->tail) {
				if (out->head == F_FP() || out->head == def->head)
					continue;
				
				G_node b = tempToNode(temp_to_node, out->head, lg.graph);

				if (!inMoveList(lg.moves, b, a)) {
					lg.moves = Live_MoveList(b, a, lg.moves);
				}
			}
		}
	}

	return lg;
}

static G_node tempToNode(TAB_table tb, Temp_temp t, G_graph g){
	G_node a = TAB_look(tb, t);
	if (!a){
		a = G_Node(g, t);
		TAB_enter(tb, t, a);
	}
	return a;
}

static bool dfs_live(G_nodeList nodes){
	bool res;
	if (nodes->tail && nodes->tail->head)
		res = dfs_live(nodes->tail);
	else if (!nodes->head)
		return FALSE;	// no change
	
	G_node n = nodes->head;
	Temp_tempList in_old = *(Temp_tempList *)G_look(inTab, n);
	Temp_tempList out_old = *(Temp_tempList *)G_look(outTab, n);

	Temp_tempList in = NULL, out = NULL;

	G_nodeList succs = G_succ(n);
	for (; succs; succs = succs->tail) {
		Temp_tempList in_succ = *(Temp_tempList *)G_look(inTab, succs->head);
		out = unionTempList(out, in_succ);
	}

	in = unionTempList(FG_use(n), subTempList(out, FG_def(n)));

	bool cur_res = !isEqual(in_old, in) || !isEqual(out_old, out);

	*(Temp_tempList*)G_look(inTab, n) = in;
	*(Temp_tempList*)G_look(outTab, n) = out;

	return res || cur_res;
}

static bool loop_live(G_nodeList nodes){
	if (!nodes)
		return FALSE;
	
	G_node n = nodes->head;
	Temp_tempList in_old = *(Temp_tempList *)G_look(inTab, n);
	Temp_tempList out_old = *(Temp_tempList *)G_look(outTab, n);

	Temp_tempList in = NULL, out = NULL;

	G_nodeList succs = G_succ(n);
	for (; succs; succs = succs->tail) {
		Temp_tempList in_succ = *(Temp_tempList *)G_look(inTab, succs->head);
		out = unionTempList(out, in_succ);
	}

	in = unionTempList(FG_use(n), subTempList(out, FG_def(n)));

	bool cur_res = !isEqual(in_old, in) || !isEqual(out_old, out);

	*(Temp_tempList*)G_look(inTab, n) = in;
	*(Temp_tempList*)G_look(outTab, n) = out;

	bool res = loop_live(nodes->tail);

	return res || cur_res;
}


static Temp_tempList unionTempList(Temp_tempList a, Temp_tempList b) {
	Temp_tempList res = a;
	for (; b; b = b->tail)
		if (!inTempList(a, b->head)) 
			res = Temp_TempList(b->head, res);
	return res;
}

static Temp_tempList subTempList(Temp_tempList a, Temp_tempList b) {
	Temp_tempList res = NULL;
	for (; a; a = a->tail) 
		if (!inTempList(b, a->head)) 
			res = Temp_TempList(a->head, res);
	return res;
}

static bool isEqual(Temp_tempList a, Temp_tempList b) {
	Temp_tempList p = a;
	for (; p; p = p->tail) 
		if (!inTempList(b, p->head))
			return FALSE;

	p = b;
	for (; p; p = p->tail) 
		if (!inTempList(a, p->head)) 
			return FALSE;

	return TRUE;
}

static bool inTempList(Temp_tempList a, Temp_temp t) {
	for (; a; a = a->tail)
		if (a->head == t) 
			return TRUE;
		
	return FALSE;
}

static bool inMoveList(Live_moveList a, G_node src, G_node dst) {
	for (; a; a = a->tail) 
		if (a->src == src && a->dst == dst) 
			return TRUE;
		
	return FALSE;
}
