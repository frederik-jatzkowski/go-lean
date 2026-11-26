package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// BindingScope tracks visible Go objects and the shared allocator for locals
// and control-flow joins.
type BindingScope struct {
	Locals lean.OrderedMap[ObjectID, int]
	Next   int
}

type AllocatedBinding struct {
	Scope BindingScope
	ID    int
}

// ReserveID assigns the next IR local or join ID.
//
//golean:export
func (scope BindingScope) ReserveID() AllocatedBinding {
	next := BindingScope{Locals: scope.Locals, Next: scope.Next + 1}
	return AllocatedBinding{Scope: next, ID: scope.Next}
}

// Bind reserves an ID, recording the object only when it is visible.
//
//golean:export
func (scope BindingScope) Bind(object ObjectID, visible bool) AllocatedBinding {
	reserved := scope.ReserveID()
	if !visible {
		return reserved
	}
	named := BindingScope{Locals: scope.Locals.Insert(object, reserved.ID), Next: reserved.Scope.Next}
	return AllocatedBinding{Scope: named, ID: reserved.ID}
}

// Remove drops a binding after its case arm finishes.
//
//golean:export
func (scope BindingScope) Remove(object ObjectID) BindingScope {
	return BindingScope{Locals: scope.Locals.Erase(object), Next: scope.Next}
}
