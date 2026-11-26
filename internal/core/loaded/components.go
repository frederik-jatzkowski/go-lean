package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// GraphNode records outgoing edges in traversal order. Targets index the graph.
type GraphNode struct {
	Edges lean.Array[uint]
}

// Components contains strongly connected groups in completion order, with
// members in the order they leave Tarjan's active stack.
type Components struct {
	Groups   lean.Array[lean.Array[uint]]
	Complete bool
}

type componentFrame struct {
	Node, Index, Low, Next uint
}

type componentWalk struct {
	Graph        lean.Array[GraphNode]
	Root, Serial uint
	Frames       lean.Array[componentFrame]
	Active       lean.Array[uint]
	Indices      lean.OrderedMap[uint, uint]
	OnStack      lean.OrderedSet[uint]
	Groups       lean.Array[lean.Array[uint]]
}

func lastComponentFrame(frames lean.Array[componentFrame]) componentFrame {
	return frames.Get(frames.Size() - 1).UnwrapOr(componentFrame{Node: 0, Index: 0, Low: 0, Next: 0})
}

func enterComponentNode(w componentWalk, node uint) componentWalk {
	serial := w.Serial + 1
	frame := componentFrame{Node: node, Index: serial, Low: serial, Next: 0}
	return componentWalk{Graph: w.Graph, Root: w.Root, Serial: serial, Frames: w.Frames.Push(frame),
		Active: w.Active.Push(node), Indices: w.Indices.Insert(node, serial), OnStack: w.OnStack.Insert(node), Groups: w.Groups}
}

func scanComponentRoot(w componentWalk) componentWalk {
	advanced := componentWalk{Graph: w.Graph, Root: w.Root + 1, Serial: w.Serial,
		Frames: w.Frames, Active: w.Active, Indices: w.Indices, OnStack: w.OnStack, Groups: w.Groups}
	if w.Indices.Contains(w.Root) {
		return advanced
	}
	return enterComponentNode(advanced, w.Root)
}

func lowerIndex(first uint, second uint) uint {
	if first < second {
		return first
	}
	return second
}

func (w componentWalk) withComponentFrames(frames lean.Array[componentFrame]) componentWalk {
	return componentWalk{Graph: w.Graph, Root: w.Root, Serial: w.Serial, Frames: frames, Active: w.Active,
		Indices: w.Indices, OnStack: w.OnStack, Groups: w.Groups}
}

func stepComponentEdge(w componentWalk, frame componentFrame, target uint) componentWalk {
	pending := componentFrame{Node: frame.Node, Index: frame.Index, Low: frame.Low, Next: frame.Next + 1}
	if target >= w.Graph.Size() {
		return w.withComponentFrames(w.Frames.Pop().Push(pending))
	}
	index := w.Indices.Find(target).UnwrapOr(0)
	if index == 0 {
		return enterComponentNode(w.withComponentFrames(w.Frames.Pop().Push(pending)), target)
	}
	if w.OnStack.Contains(target) {
		updated := componentFrame{Node: frame.Node, Index: frame.Index, Low: lowerIndex(frame.Low, index), Next: pending.Next}
		return w.withComponentFrames(w.Frames.Pop().Push(updated))
	}
	return w.withComponentFrames(w.Frames.Pop().Push(pending))
}

type popComponent struct {
	Root    uint
	Active  lean.Array[uint]
	OnStack lean.OrderedSet[uint]
	Group   lean.Array[uint]
}

func stepPopComponent(_ uint, state popComponent) lean.FoldControl[popComponent] {
	node := state.Active.Get(state.Active.Size() - 1).UnwrapOr(0)
	next := popComponent{Root: state.Root, Active: state.Active.Pop(),
		OnStack: state.OnStack.Erase(node), Group: state.Group.Push(node)}
	return lean.FoldControl[popComponent]{State: next, Stop: node == state.Root}
}

func finishComponentNode(w componentWalk, frame componentFrame) componentWalk {
	rest := w.Frames.Pop()
	parent := updateComponentParent(rest, frame.Low)
	if frame.Low != frame.Index {
		return w.withComponentFrames(parent)
	}
	initial := popComponent{Root: frame.Node, Active: w.Active, OnStack: w.OnStack, Group: lean.Array[uint]{}}
	result := lean.FoldNUntil(w.Active.Size(), initial, stepPopComponent)
	return componentWalk{Graph: w.Graph, Root: w.Root, Serial: w.Serial, Frames: parent,
		Active: result.State.Active, Indices: w.Indices, OnStack: result.State.OnStack, Groups: w.Groups.Push(result.State.Group)}
}

func updateComponentParent(frames lean.Array[componentFrame], low uint) lean.Array[componentFrame] {
	if frames.Size() == 0 {
		return frames
	}
	parent := lastComponentFrame(frames)
	updated := componentFrame{Node: parent.Node, Index: parent.Index, Low: lowerIndex(parent.Low, low), Next: parent.Next}
	return frames.Pop().Push(updated)
}

func (w componentWalk) complete() bool {
	return w.Root >= w.Graph.Size() && w.Frames.Size() == 0
}

func stepComponentWalk(_ uint, w componentWalk) lean.FoldControl[componentWalk] {
	if w.complete() {
		return lean.FoldControl[componentWalk]{State: w, Stop: true}
	}
	next := advanceComponentWalk(w)
	return lean.FoldControl[componentWalk]{State: next, Stop: next.complete()}
}

func advanceComponentWalk(w componentWalk) componentWalk {
	if w.Frames.Size() == 0 {
		return scanComponentRoot(w)
	}
	frame := lastComponentFrame(w.Frames)
	edges := w.Graph.Get(frame.Node).UnwrapOr(GraphNode{Edges: lean.Array[uint]{}}).Edges
	if frame.Next >= edges.Size() {
		return finishComponentNode(w, frame)
	}
	return stepComponentEdge(w, frame, edges.Get(frame.Next).UnwrapOr(w.Graph.Size()))
}

func grantComponentSteps(node uint, w componentWalk) lean.FoldControl[componentWalk] {
	slots := lean.FoldNUntil(2, w, stepComponentWalk)
	if slots.Stop {
		return slots
	}
	edges := w.Graph.Get(node).UnwrapOr(GraphNode{Edges: lean.Array[uint]{}}).Edges
	return lean.FoldNUntil(edges.Size(), slots.State, stepComponentWalk)
}

// StrongComponents runs Tarjan's traversal with explicit call frames. Each
// step scans one root, advances one edge, or completes one node. The outer
// fold supplies two steps per node plus one per edge, without adding counts
// that could overflow a machine word.
//
//golean:export
func StrongComponents(graph lean.Array[GraphNode]) Components {
	initial := componentWalk{Graph: graph, Root: 0, Serial: 0, Frames: lean.Array[componentFrame]{},
		Active: lean.Array[uint]{}, Indices: lean.OrderedMap[uint, uint]{},
		OnStack: lean.OrderedSet[uint]{}, Groups: lean.Array[lean.Array[uint]]{}}
	result := lean.FoldNUntil(graph.Size(), initial, grantComponentSteps)
	return Components{Groups: result.State.Groups, Complete: result.State.complete()}
}
