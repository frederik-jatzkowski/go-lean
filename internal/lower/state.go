package lower

import (
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"maps"
	"math"
)

type functionFact struct{ function, kind int64 }

type stateSnapshot struct {
	bindings map[int64]int64
	facts    map[functionFact]int64
	next     int64
}

func (s stateSnapshot) HasBinding(value int64) bool {
	_, ok := s.bindings[value]
	return ok
}

func (s stateSnapshot) LookupBinding(value int64) int64 { return s.bindings[value] }

func (s stateSnapshot) Bind(value, binder int64) StateStore {
	s.bindings = setEntry(s.bindings, value, binder)
	return s
}

func (s stateSnapshot) HasFact(function, kind int64) bool {
	_, ok := s.facts[functionFact{function, kind}]
	return ok
}

func (s stateSnapshot) LookupFact(function, kind int64) int64 {
	return s.facts[functionFact{function, kind}]
}

func (s stateSnapshot) PutFact(function, kind, value int64) StateStore {
	s.facts = setEntry(s.facts, functionFact{function, kind}, value)
	return s
}

func (s stateSnapshot) NextID() int64 { return s.next }

func (s stateSnapshot) Advance() StateStore {
	if s.next < math.MaxInt64 {
		s.next++
	}
	return s
}

func (s stateSnapshot) WithCursor(cursor int64) StateStore {
	s.next = max(0, cursor)
	return s
}

func setEntry[K comparable](entries map[K]int64, key K, value int64) map[K]int64 {
	next := maps.Clone(entries)
	if next == nil {
		next = make(map[K]int64)
	}
	next[key] = value
	return next
}

// restoreBindings restores the incoming branch while keeping allocations made
// in the previous branch out of the rest of the function's ID stream.
func restoreBindings(parent StateStore, after StateStore) StateStore {
	return parent.WithCursor(after.NextID())
}

func (l *lowerer) binding(value *sourceValue) (ir.Binder, bool) {
	index, ok := lookupBindingID(l.state, value.ID)
	if !ok {
		return ir.Binder{}, false
	}
	return (*l.binders)[index], true
}

func (l *lowerer) mustBinding(value *sourceValue) ir.Binder {
	binder, ok := l.binding(value)
	if !ok {
		panic("missing binding for checked SSA value: " + value.Name)
	}
	return binder
}

func (l *lowerer) phiValue(phi *sourceValue, predecessor *sourceBlock, value func(*sourceValue) ir.Expr) ir.Expr {
	var predID int64
	if predecessor != nil {
		predID = predecessor.ID
	}
	operand, index, incoming, bound := resolveIncoming(l.input, l.state, phi.ID, predID)
	if !incoming {
		panic("checked SSA phi has no operand for the current predecessor")
	}
	if bound {
		return ir.Ref((*l.binders)[index])
	}
	for _, edge := range phi.Values {
		if edge.ID == operand {
			return value(edge)
		}
	}
	panic("input phi selected an operand outside its edge list")
}

const (
	effectFact int64 = iota
	dependencyFact
)

type functionFacts struct {
	store        StateStore
	dependencies [][]ir.Type
}

func (f *functionFacts) record(fn *sourceFunction, effect bool, dependencies []ir.Type) {
	f.store = recordEmission(f.store, fn.ID, effect)
	if len(dependencies) > 0 {
		f.store = f.store.PutFact(fn.ID, dependencyFact, int64(len(f.dependencies)))
		f.dependencies = append(f.dependencies, dependencies)
	}
}

func (f *functionFacts) effect(fn *sourceFunction) bool {
	effect, found := lookupEmission(f.store, fn.ID)
	if !found {
		panic("missing emission fact for checked callee: " + fn.Name)
	}
	return effect
}

func (f *functionFacts) contracts(fn *sourceFunction) []ir.Type {
	if !f.store.HasFact(fn.ID, dependencyFact) {
		return nil
	}
	return f.dependencies[f.store.LookupFact(fn.ID, dependencyFact)]
}
