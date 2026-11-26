package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// CheckedTypeEdge is a named reference found in a checked declaration.
type CheckedTypeEdge struct {
	Target ObjectID
	Direct bool
}

// CheckedTypeEdges walks a checked field type in recursion-diagnostic order.
//
//golean:export
func CheckedTypeEdges(t CheckedType) lean.List[CheckedTypeEdge] {
	return checkedTypeEdges(t, true, lean.List[CheckedTypeEdge]{})
}

//golean:termination:by sizeOf t
func checkedTypeEdges(t CheckedType, direct bool, tail lean.List[CheckedTypeEdge]) lean.List[CheckedTypeEdge] {
	if t.Kind == RecordShape || t.Kind == EnumShape {
		return lean.Cons(CheckedTypeEdge{Target: t.Object, Direct: direct}, tail)
	}
	if t.Kind != CuratedShape {
		return tail
	}
	if t.First.IsSome() {
		first := t.First.Get()
		if t.Curated == CuratedBox {
			nextDirect := direct && (first.Kind == RecordShape || first.Kind == EnumShape)
			return checkedTypeEdges(first, nextDirect, tail)
		}
		if t.Curated == CuratedMap {
			if t.Second.IsSome() {
				keys := checkedTypeEdges(first, false, tail)
				return checkedTypeEdges(t.Second.Get(), false, keys)
			}
		}
		return checkedTypeEdges(first, false, tail)
	}
	return tail
}
