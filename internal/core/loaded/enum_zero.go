package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// EnumZeroCheck reports a cycle in the default value, in traversal order.
// Exhausted indicates that the traversal exceeded its input-derived bound.
type EnumZeroCheck struct {
	Cycle     lean.Array[string]
	Exhausted bool
}

type zeroFrame struct {
	Type     TypeID
	Object   ObjectID
	Next     uint
	Children lean.Array[ObjectID]
	Default  string
	Enum     bool
}

type zeroWalk struct {
	Program Program
	Stack   lean.Array[zeroFrame]
	Status  lean.OrderedMap[ObjectID, uint8]
	Path    lean.Array[string]
	Cycle   lean.Array[string]
}

const (
	zeroActive uint8 = 1
	zeroDone   uint8 = 2
)

func noZeroFrame() zeroFrame {
	return zeroFrame{Type: 0, Object: 0, Next: 0, Children: lean.Array[ObjectID]{}, Default: "", Enum: false}
}

func enterZeroType(id TypeID) zeroFrame {
	return zeroFrame{Type: id, Object: 0, Next: 0, Children: lean.Array[ObjectID]{}, Default: "", Enum: false}
}

func (w zeroWalk) withStack(stack lean.Array[zeroFrame]) zeroWalk {
	return zeroWalk{Program: w.Program, Stack: stack, Status: w.Status, Path: w.Path, Cycle: w.Cycle}
}

func zeroChildren(t Type, entry Object, underlying Type) zeroFrame {
	if entry.Enum.IsSome() {
		spec := entry.Enum.UnwrapOr(Enum{Payloads: lean.Array[ObjectID]{}, Default: ""})
		return zeroFrame{Type: 0, Object: t.Object, Next: 0, Children: spec.Payloads, Default: spec.Default, Enum: true}
	}
	return zeroFrame{Type: 0, Object: t.Object, Next: 0, Children: underlying.Fields, Default: "", Enum: false}
}

func visitZeroType(w zeroWalk, frame zeroFrame, rest lean.Array[zeroFrame]) zeroWalk {
	t := w.Program.Unalias(frame.Type)
	if t.Kind != NamedType {
		return w.withStack(rest)
	}
	entry := w.Program.LookupObject(t.Object).UnwrapOr(emptyLoadedObject())
	if entry.Package == Curated {
		if entry.Name == "FoldControl" {
			return w.withStack(rest.Push(enterZeroType(t.Args.Get(0).UnwrapOr(0))))
		}
		return w.withStack(rest)
	}
	status := w.Status.Find(t.Object).UnwrapOr(0)
	if status == zeroActive {
		return zeroWalk{Program: w.Program, Stack: rest, Status: w.Status, Path: w.Path, Cycle: w.Path.Push(entry.Name)}
	}
	if status == zeroDone {
		return w.withStack(rest)
	}
	fields := w.Program.LookupType(t.Underlying).UnwrapOr(emptyLoadedType())
	next := rest.Push(zeroChildren(t, entry, fields))
	return zeroWalk{Program: w.Program, Stack: next, Status: w.Status.Insert(t.Object, zeroActive),
		Path: w.Path.Push(entry.Name), Cycle: w.Cycle}
}

func visitZeroChild(w zeroWalk, frame zeroFrame, rest lean.Array[zeroFrame]) zeroWalk {
	if frame.Next >= frame.Children.Size() {
		return zeroWalk{Program: w.Program, Stack: rest, Status: w.Status.Insert(frame.Object, zeroDone),
			Path: w.Path.Pop(), Cycle: w.Cycle}
	}
	child := frame.Children.Get(frame.Next).UnwrapOr(0)
	entry := w.Program.LookupObject(child).UnwrapOr(emptyLoadedObject())
	next := zeroFrame{Type: 0, Object: frame.Object, Next: frame.Next + 1, Children: frame.Children,
		Default: frame.Default, Enum: frame.Enum}
	stack := rest.Push(next)
	if frame.Enum && entry.Name != frame.Default {
		return w.withStack(stack)
	}
	return w.withStack(stack.Push(enterZeroType(entry.Type)))
}

func advanceZeroWalk(w zeroWalk) zeroWalk {
	frame := w.Stack.Get(w.Stack.Size() - 1).UnwrapOr(noZeroFrame())
	rest := w.Stack.Pop()
	if frame.Object == 0 {
		return visitZeroType(w, frame, rest)
	}
	return visitZeroChild(w, frame, rest)
}

func stepZeroWalk(_ uint, w zeroWalk) lean.FoldControl[zeroWalk] {
	if w.Stack.Size() == 0 || w.Cycle.Size() != 0 {
		return lean.FoldControl[zeroWalk]{State: w, Stop: true}
	}
	next := advanceZeroWalk(w)
	return lean.FoldControl[zeroWalk]{State: next, Stop: next.Stack.Size() == 0 || next.Cycle.Size() != 0}
}

func zeroTypeSteps(_ uint, w zeroWalk) lean.FoldControl[zeroWalk] {
	return lean.FoldNUntil(w.Program.Types.Size(), w, stepZeroWalk)
}

func zeroEdgeSteps(_ uint, w zeroWalk) lean.FoldControl[zeroWalk] {
	return lean.FoldNUntil(w.Program.Objects.Size(), w, zeroTypeSteps)
}

func zeroNodeSteps(_ uint, w zeroWalk) lean.FoldControl[zeroWalk] {
	return lean.FoldNUntil(w.Program.Objects.Size(), w, zeroEdgeSteps)
}

// CheckEnumZero follows the fields used to construct a zero value. Named
// types are entered once, and each field can traverse at most one chain of
// FoldControl instantiations before reaching another named type. Three
// batches cover entering frames, advancing edges, and completing frames.
// Nested folds keep the bound independent of machine-word multiplication.
//
//golean:export
func (p Program) CheckEnumZero(id ObjectID) EnumZeroCheck {
	if id == 0 || uint(id) >= p.Objects.Size() || p.Types.Size() == 0 {
		return EnumZeroCheck{Cycle: lean.Array[string]{}, Exhausted: false}
	}
	root := p.LookupObject(id).UnwrapOr(emptyLoadedObject())
	initial := zeroWalk{Program: p, Stack: lean.Array[zeroFrame]{}.Push(enterZeroType(root.Type)),
		Status: lean.OrderedMap[ObjectID, uint8]{}, Path: lean.Array[string]{}, Cycle: lean.Array[string]{}}
	walked := lean.FoldNUntil(3, initial, zeroNodeSteps)
	return EnumZeroCheck{Cycle: walked.State.Cycle, Exhausted: !walked.Stop}
}
