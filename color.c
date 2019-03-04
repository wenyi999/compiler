#include <stdio.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "table.h"

#define K 15

static void Build(G_graph ig);
static int locate_register(Temp_temp temp);
static void MakeWorklist(G_graph ig);
static void Simplify();
static void DecrementDegree(G_node m);
static void EnableMoves(G_nodeList nodes);
static void Coalesce();
static G_nodeList Adjacent(G_node n);
static void AddWorkList(G_node u);
static bool OK(G_node t, G_node r);
static bool Briggs(G_node u, G_node v);
static void Combine(G_node u, G_node v);
static void Freeze();
static void FreezeMoves(G_node u);
static void SelectSpill();
static void AssignColors(G_graph ig);
static bool MoveRelated(G_node n);
static Live_moveList NodeMoves(G_node n);
static G_node GetAlias(G_node n);
static bool inMoveList(Live_moveList a, G_node src, G_node dst);
static Live_moveList subMoveList(Live_moveList a, Live_moveList b);
static Live_moveList unionMoveList(Live_moveList a, Live_moveList b);
static bool precolored(G_node n);
static void AddEdge(G_node u, G_node v);
static G_nodeList G_subNodeList(G_nodeList u, G_nodeList v);
static G_nodeList G_unionNodeList(G_nodeList u, G_nodeList v);

static bool inTempList(Temp_tempList a, Temp_temp t);

static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;
static G_nodeList spillWorklist;

static G_nodeList spilledNodes;
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
static G_nodeList selectStack;

static Live_moveList coalescedMoves;
static Live_moveList constrainedMoves;
static Live_moveList frozenMoves;
static Live_moveList worklistMoves;
static Live_moveList activeMoves;

static Temp_tempList notSpillTemps;

static void enter_hard_regs(Temp_map coloring);

static G_table degreeTab;
static G_table colorTab;
static G_table aliasTab;

static char *hard_regs[17] = {"none", "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15", "%rsp"};

struct COL_result COL_color(G_graph ig, Temp_map initial, Temp_tempList regs, Live_moveList moves, Temp_tempList nst)
{
	// initial
	simplifyWorklist = NULL;
	freezeWorklist = NULL;
	spillWorklist = NULL;

	spilledNodes = NULL;
	coalescedNodes = NULL;
	coloredNodes = NULL;
	selectStack = NULL;

	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = moves;
	activeMoves = NULL;

	notSpillTemps = nst;

	degreeTab = G_empty();
	colorTab = G_empty();
	aliasTab = G_empty();

	Build(ig);

	MakeWorklist(ig);

	while (simplifyWorklist || worklistMoves || freezeWorklist || spillWorklist)
	{
		if (simplifyWorklist)
		{
			Simplify();
		}
		else if (worklistMoves)
		{
			Coalesce();
		}
		else if (freezeWorklist)
		{
			Freeze();
		}
		else if (spillWorklist)
		{
			SelectSpill();
		}
	}

	AssignColors(ig);
	struct COL_result ret;
	Temp_map coloring = Temp_empty();
	G_nodeList nodes = G_nodes(ig);
	// enter_hard_regs(coloring);
	for (; nodes; nodes = nodes->tail)
	{
		int *color = G_look(colorTab, GetAlias(nodes->head));
		Temp_enter(coloring, Live_gtemp(nodes->head), hard_regs[*color]);
	}

	ret.coloring = coloring;

	Temp_tempList actual_spills = NULL;

    for (; spilledNodes; spilledNodes = spilledNodes->tail) {
        Temp_temp temp = G_nodeInfo(spilledNodes->head);
        actual_spills = Temp_TempList(temp, actual_spills);
    }

	ret.spills = actual_spills;
	return ret;
}

static void Build(G_graph ig)
{
	int i = 0;
	G_nodeList nodes;
	for (nodes = G_nodes(ig); nodes; nodes = nodes->tail)
	{
		// printf("node: %d\n", i++);
		/* intial degree */
		int *degree = checked_malloc(sizeof(int));
		*degree = 0;
		G_nodeList cur;
		for (cur = G_succ(nodes->head); cur; cur = cur->tail)
		{
			(*degree)++;
		}
		G_enter(degreeTab, nodes->head, degree);

		/* intial color */
		int *color = checked_malloc(sizeof(int));
		Temp_temp temp = Live_gtemp(nodes->head);
		*color = locate_register(temp);

		G_enter(colorTab, nodes->head, color);

		/* initial alias */
		G_node *alias = checked_malloc(sizeof(G_node));
		*alias = nodes->head;
		G_enter(aliasTab, nodes->head, alias);
	}
}

static int locate_register(Temp_temp temp)
{
	if (temp == F_RAX())
		return 1;
	else if (temp == F_RBX())
		return 2;
	else if (temp == F_RCX())
		return 3;
	else if (temp == F_RDX())
		return 4;
	else if (temp == F_RSI())
		return 5;
	else if (temp == F_RDI())
		return 6;
	else if (temp == F_RBP())
		return 7;
	else if (temp == F_R8())
		return 8;
	else if (temp == F_R9())
		return 9;
	else if (temp == F_R10())
		return 10;
	else if (temp == F_R11())
		return 11;
	else if (temp == F_R12())
		return 12;
	else if (temp == F_R13())
		return 13;
	else if (temp == F_R14())
		return 14;
	else if (temp == F_R15())
		return 15;
	else if (temp == F_RSP())
		return 16;
	else if (temp == F_FP())
		assert(0);

	return 0;
}

static void MakeWorklist(G_graph ig)
{
	G_nodeList nodes;
	for (nodes = G_nodes(ig); nodes; nodes = nodes->tail)
	{
		int *degree = G_look(degreeTab, nodes->head);
		int *color = G_look(colorTab, nodes->head);

		if (*color != 0)
		{
			continue;
		}

		if (*degree >= K)
		{
			spillWorklist = G_NodeList(nodes->head, spillWorklist);
		}
		else if (MoveRelated(nodes->head))
		{
			freezeWorklist = G_NodeList(nodes->head, freezeWorklist);
		}
		else
		{
			simplifyWorklist = G_NodeList(nodes->head, simplifyWorklist);
		}
	}
}

static void Simplify()
{
	G_node n = simplifyWorklist->head;
	simplifyWorklist = simplifyWorklist->tail;
	selectStack = G_NodeList(n, selectStack);
	G_nodeList nodes;
	for (nodes = Adjacent(n); nodes; nodes = nodes->tail)
		DecrementDegree(nodes->head);
	// check adjacent nodes
}

static void DecrementDegree(G_node m)
{
	int *color = G_look(colorTab, m);
	if (*color != 0)
		return;

	int *degree = G_look(degreeTab, m);
	(*degree)--;

	// here ==, because nodes whose degree < K has be included in simplifyWorklist.
	if (*degree == K - 1)
	{
		EnableMoves(G_NodeList(m, Adjacent(m)));
		spillWorklist = G_subNodeList(spillWorklist, G_NodeList(m, NULL));
		if (MoveRelated(m))
		{
			freezeWorklist = G_NodeList(m, freezeWorklist);
		}
		else
		{
			simplifyWorklist = G_NodeList(m, simplifyWorklist);
		}
	}
}

static void EnableMoves(G_nodeList nodes)
{
	for (; nodes; nodes = nodes->tail)
	{
		G_node n = nodes->head;
		Live_moveList m;
		for (m = NodeMoves(n); m; m = m->tail)
		{
			if (inMoveList(activeMoves, m->src, m->dst))
			{
				activeMoves = subMoveList(activeMoves, Live_MoveList(m->src, m->dst, NULL));
				worklistMoves = Live_MoveList(m->src, m->dst, worklistMoves);
			}
		}
	}
}

static void Coalesce()
{
	G_node u, v;
	G_node x = worklistMoves->src;
	G_node y = worklistMoves->dst;

	// guarantee at least one is 0 color.   bind v to u.
	if (precolored(GetAlias(y)))
	{
		u = GetAlias(y);
		v = GetAlias(x);
	}
	else
	{
		u = GetAlias(x);
		v = GetAlias(y);
	}
	worklistMoves = worklistMoves->tail;
	if (u == v)
	{
		coalescedMoves = Live_MoveList(x, y, coalescedMoves);
		AddWorkList(u);
	}
	else if (precolored(v) || G_inNodeList(u, G_adj(v)))
	{
		constrainedMoves = Live_MoveList(x, y, constrainedMoves);
		AddWorkList(u);
		AddWorkList(v);
	}
	else if (precolored(u) && (OK(v, u)))
	{
		coalescedMoves = Live_MoveList(x, y, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else if (!precolored(u) && Briggs(u, v))
	{
		coalescedMoves = Live_MoveList(x, y, coalescedMoves);
		Combine(u, v);
		AddWorkList(u);
	}
	else
	{
		activeMoves = Live_MoveList(x, y, activeMoves);
	}
}

static G_nodeList Adjacent(G_node n)
{
	return G_subNodeList(G_subNodeList(G_succ(n), selectStack), coalescedNodes);
}

static void AddWorkList(G_node u)
{
	if (!precolored(u) && !MoveRelated(u) && *(int *)G_look(degreeTab, u) < K)
	{
		freezeWorklist = G_subNodeList(freezeWorklist, G_NodeList(u, NULL));
		simplifyWorklist = G_NodeList(u, simplifyWorklist);
	}
}

// foreach t's adjacent
static bool OK(G_node t, G_node r)
{
	G_nodeList p;
	for (p = Adjacent(t); p; p = p->tail)
	{
		if (*(int *)G_look(degreeTab, p->head) < K || precolored(p->head) || G_inNodeList(p->head, G_adj(r)))
		{
			continue;
		}
		else
		{
			return FALSE;
		}
	}
	return TRUE;
}

static bool Briggs(G_node u, G_node v)
{
	G_nodeList nodes = G_unionNodeList(Adjacent(u), Adjacent(v));
	int k = 0;
	for (; nodes; nodes = nodes->tail)
	{
		G_node n = nodes->head;
		if (*(int *)G_look(degreeTab, n) >= K)
		{
			k++;
		}
	}
	return (k < K);
}

// bind v to u
static void Combine(G_node u, G_node v)
{
	if (G_inNodeList(v, freezeWorklist))
	{
		freezeWorklist = G_subNodeList(freezeWorklist, G_NodeList(v, NULL));
	}
	else
	{
		spillWorklist = G_subNodeList(spillWorklist, G_NodeList(v, NULL));
	}
	coalescedNodes = G_NodeList(v, coalescedNodes);

	// amazing data structrue...
	*(G_node *)G_look(aliasTab, v) = u;
	G_nodeList t;
	for (t = Adjacent(v); t; t = t->tail)
	{
		AddEdge(t->head, u);
		DecrementDegree(t->head);
	}

	if (*(int *)G_look(degreeTab, u) >= K && G_inNodeList(u, freezeWorklist))
	{
		freezeWorklist = G_subNodeList(freezeWorklist, G_NodeList(u, NULL));
		spillWorklist = G_NodeList(u, spillWorklist);
	}
}

static void Freeze()
{
	G_node u = freezeWorklist->head;
	freezeWorklist = freezeWorklist->tail;
	simplifyWorklist = G_NodeList(u, simplifyWorklist);
	FreezeMoves(u);
}

static void FreezeMoves(G_node u)
{
	Live_moveList m;
	for (m = NodeMoves(u); m; m = m->tail)
	{
		G_node x = m->src;
		G_node y = m->dst;
		G_node v;
		if (GetAlias(y) == GetAlias(u))
		{
			v = GetAlias(x);
		}
		else
		{
			v = GetAlias(y);
		}
		activeMoves = subMoveList(activeMoves, Live_MoveList(x, y, NULL));
		frozenMoves = Live_MoveList(x, y, frozenMoves);
		if (NodeMoves(v) == NULL && *(int *)G_look(degreeTab, v) < K)
		{
			freezeWorklist = G_subNodeList(freezeWorklist, G_NodeList(v, NULL));
			simplifyWorklist = G_NodeList(v, simplifyWorklist);
		}
	}
}

static void SelectSpill()
{
	G_node m = NULL;
	int max = 0;
	G_nodeList p;
	for (p = spillWorklist; p; p = p->tail)
	{
		Temp_temp t = G_nodeInfo(p->head);
		if (inTempList(notSpillTemps, t))
		{
			continue;
		}
		int degree = *(int *)G_look(degreeTab, p->head);
		if (degree > max)
		{
			max = degree;
			m = p->head;
		}
	}

	if (m)
	{
		spillWorklist = G_subNodeList(spillWorklist, G_NodeList(m, NULL));
		simplifyWorklist = G_NodeList(m, simplifyWorklist);
		FreezeMoves(m);
	}
	else
	{
		assert(0);
	}
}

static void AssignColors(G_graph ig)
{
	bool okColors[K + 2];

	spilledNodes = NULL;
	while (selectStack)
	{
		okColors[0] = FALSE;
		int i;
		for (i = 1; i < K + 1; i++)
		{
			okColors[i] = TRUE;
		}

		G_node n = selectStack->head;
		selectStack = selectStack->tail;
		G_nodeList adjs;
		for (adjs = G_succ(n); adjs; adjs = adjs->tail)
		{
			int *color = G_look(colorTab, GetAlias(adjs->head));
			okColors[*color] = FALSE;
		}

		int i;
		bool realSpill = TRUE;
		for (i = 1; i < K + 1; i++)
		{
			if (okColors[i])
			{
				realSpill = FALSE;
				break;
			}
		}

		if (realSpill)
		{
			spilledNodes = G_NodeList(n, spilledNodes);
		}
		else
		{
			*(int *)G_look(colorTab, n) = i;
		}
	}

	// color coalesced nodes
	G_nodeList p;
	for (p = G_nodes(ig); p; p = p->tail)
	{
		*(int *)G_look(colorTab, p->head) = *(int *)G_look(colorTab, GetAlias(p->head));
	}
}

static bool MoveRelated(G_node n)
{
	return (NodeMoves(n) != NULL);
}

// search n in movelist.
static Live_moveList NodeMoves(G_node n)
{
	Live_moveList moves = NULL;
	G_node m = GetAlias(n);
	Live_moveList p;
	for (p = unionMoveList(activeMoves, worklistMoves); p; p = p->tail)
		if (GetAlias(p->src) == m || GetAlias(p->dst) == m)
			moves = Live_MoveList(p->src, p->dst, moves);
	return moves;
}

// find the original one
static G_node GetAlias(G_node n)
{
	assert(n);
	G_node *res = G_look(aliasTab, n);
	if (*res != n)
		return GetAlias(*res);
	return *res;
}

static Live_moveList unionMoveList(Live_moveList a, Live_moveList b)
{
	Live_moveList res = a;
	Live_moveList p;
	for (p = b; p; p = p->tail)
		if (!inMoveList(a, p->src, p->dst))
			res = Live_MoveList(p->src, p->dst, res);
	return res;
}

static Live_moveList subMoveList(Live_moveList a, Live_moveList b)
{
	Live_moveList res = NULL;
	Live_moveList p;
	for (p = a; p; p = p->tail)
		if (!inMoveList(b, p->src, p->dst))
			res = Live_MoveList(p->src, p->dst, res);
	return res;
}

static bool inMoveList(Live_moveList a, G_node src, G_node dst)
{
	for (; a; a = a->tail)
		if (a->src == src && a->dst == dst)
			return TRUE;

	return FALSE;
}

static bool precolored(G_node n)
{
	assert(n);
	return *(int *)G_look(colorTab, n);
}

static void AddEdge(G_node u, G_node v)
{
	if (!G_inNodeList(u, G_adj(v)) && u != v)
	{
		if (!precolored(u))
		{
			(*(int *)G_look(degreeTab, u))++;
			G_addEdge(u, v);
		}
		if (!precolored(v))
		{
			(*(int *)G_look(degreeTab, v))++;
			G_addEdge(v, u);
		}
	}
}

static G_nodeList G_subNodeList(G_nodeList u, G_nodeList v)
{
	G_nodeList res = NULL;
	G_nodeList nodes;
	for (nodes = u; nodes; nodes = nodes->tail)
		if (!G_inNodeList(nodes->head, v))
			res = G_NodeList(nodes->head, res);
	return res;
}
static G_nodeList G_unionNodeList(G_nodeList u, G_nodeList v)
{
	G_nodeList res = u;
	G_nodeList nodes;
	for (nodes = v; nodes; nodes = nodes->tail)
		if (!G_inNodeList(nodes->head, u))
			res = G_NodeList(nodes->head, res);
	return res;
}

static void enter_hard_regs(Temp_map coloring)
{
	Temp_enter(coloring, F_RAX(), hard_regs[1]);
	Temp_enter(coloring, F_RBX(), hard_regs[2]);
	Temp_enter(coloring, F_RCX(), hard_regs[3]);
	Temp_enter(coloring, F_RDX(), hard_regs[4]);
	Temp_enter(coloring, F_RSI(), hard_regs[5]);
	Temp_enter(coloring, F_RDI(), hard_regs[6]);
	Temp_enter(coloring, F_RBP(), hard_regs[7]);
	Temp_enter(coloring, F_R8(), hard_regs[8]);
	Temp_enter(coloring, F_R9(), hard_regs[9]);
	Temp_enter(coloring, F_R10(), hard_regs[10]);
	Temp_enter(coloring, F_R11(), hard_regs[11]);
	Temp_enter(coloring, F_R12(), hard_regs[12]);
	Temp_enter(coloring, F_R13(), hard_regs[13]);
	Temp_enter(coloring, F_R14(), hard_regs[14]);
	Temp_enter(coloring, F_R15(), hard_regs[15]);
	Temp_enter(coloring, F_RSP(), hard_regs[16]);
}

static bool inTempList(Temp_tempList a, Temp_temp t)
{
	for (; a; a = a->tail)
		if (a->head == t)
			return TRUE;
	return FALSE;
}
