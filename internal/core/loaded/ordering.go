package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// GraphPlacement schedules a node before the root that first reached it.
type GraphPlacement struct {
	RootIndex, Node uint
}

type DependencyOrder struct {
	Placements lean.Array[GraphPlacement]
	Complete   bool
}

type orderFrame struct {
	Node, Next uint
}

type orderWalk struct {
	Graph      lean.Array[GraphNode]
	Roots      lean.Array[uint]
	NextRoot   uint
	Frames     lean.Array[orderFrame]
	Seen       lean.OrderedSet[uint]
	Placements lean.Array[GraphPlacement]
}

func enterOrderNode(w orderWalk, node uint) orderWalk {
	if node >= w.Graph.Size() || w.Seen.Contains(node) {
		return w
	}
	next := orderFrame{Node: node, Next: 0}
	return orderWalk{Graph: w.Graph, Roots: w.Roots, NextRoot: w.NextRoot, Frames: w.Frames.Push(next),
		Seen: w.Seen.Insert(node), Placements: w.Placements}
}

func advanceOrder(w orderWalk) orderWalk {
	if w.Frames.Size() == 0 {
		node := w.Roots.Get(w.NextRoot).UnwrapOr(w.Graph.Size())
		next := orderWalk{Graph: w.Graph, Roots: w.Roots, NextRoot: w.NextRoot + 1, Frames: w.Frames,
			Seen: w.Seen, Placements: w.Placements}
		return enterOrderNode(next, node)
	}
	frame := w.Frames.Get(w.Frames.Size() - 1).UnwrapOr(orderFrame{Node: 0, Next: 0})
	rest := w.Frames.Pop()
	edges := w.Graph.Get(frame.Node).UnwrapOr(GraphNode{Edges: lean.Array[uint]{}}).Edges
	if frame.Next >= edges.Size() {
		placement := GraphPlacement{RootIndex: w.NextRoot - 1, Node: frame.Node}
		return orderWalk{Graph: w.Graph, Roots: w.Roots, NextRoot: w.NextRoot, Frames: rest,
			Seen: w.Seen, Placements: w.Placements.Push(placement)}
	}
	pending := orderFrame{Node: frame.Node, Next: frame.Next + 1}
	advanced := orderWalk{Graph: w.Graph, Roots: w.Roots, NextRoot: w.NextRoot, Frames: rest.Push(pending),
		Seen: w.Seen, Placements: w.Placements}
	return enterOrderNode(advanced, edges.Get(frame.Next).UnwrapOr(w.Graph.Size()))
}

func (w orderWalk) complete() bool {
	return w.NextRoot >= w.Roots.Size() && w.Frames.Size() == 0
}

func stepOrder(_ uint, w orderWalk) lean.FoldControl[orderWalk] {
	if w.complete() {
		return lean.FoldControl[orderWalk]{State: w, Stop: true}
	}
	next := advanceOrder(w)
	return lean.FoldControl[orderWalk]{State: next, Stop: next.complete()}
}

func grantOrderEdges(node uint, w orderWalk) lean.FoldControl[orderWalk] {
	edges := w.Graph.Get(node).UnwrapOr(GraphNode{Edges: lean.Array[uint]{}}).Edges
	return lean.FoldNUntil(edges.Size(), w, stepOrder)
}

// OrderDependencies schedules reachable graph nodes after their dependencies.
// It scans roots and edges in input order. An out-of-range root has no node,
// which lets callers keep entries that are interleaved with the graph roots.
//
//golean:export
func OrderDependencies(graph lean.Array[GraphNode], roots lean.Array[uint]) DependencyOrder {
	initial := orderWalk{Graph: graph, Roots: roots, NextRoot: 0, Frames: lean.Array[orderFrame]{},
		Seen: lean.OrderedSet[uint]{}, Placements: lean.Array[GraphPlacement]{}}
	afterRoots := lean.FoldNUntil(roots.Size(), initial, stepOrder)
	afterNodes := lean.FoldNUntil(graph.Size(), afterRoots.State, stepOrder)
	afterEdges := lean.FoldNUntil(graph.Size(), afterNodes.State, grantOrderEdges)
	return DependencyOrder{Placements: afterEdges.State.Placements, Complete: afterEdges.State.complete()}
}
