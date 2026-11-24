package lower

import (
	"fmt"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

type typeEdge struct {
	target    ir.Symbol
	supported bool
}

func typeEdges(t ir.Type, direct bool) []typeEdge {
	switch t.Kind {
	case ir.Record, ir.EnumType:
		return []typeEdge{{target: t.Record, supported: direct}}
	case ir.Box:
		return typeEdges(*t.Element, direct && (t.Element.Kind == ir.Record || t.Element.Kind == ir.EnumType))
	default:
		var edges []typeEdge
		if t.Element != nil {
			edges = append(edges, typeEdges(*t.Element, false)...)
		}
		if t.Key != nil {
			edges = append(edges, typeEdges(*t.Key, false)...)
		}
		return edges
	}
}

// Group recursive type declarations while keeping ordinary declaration order.
// A group can pull in a type dependency that originally followed its first member.
func groupTypes(pkg *ir.Package) error {
	decls := make(map[ir.Symbol]ir.Declaration)
	edges := make(map[ir.Symbol][]typeEdge)
	var order []ir.Symbol
	symbol := func(decl ir.Declaration) ir.Symbol {
		switch d := decl.(type) {
		case ir.Enum:
			return d.Symbol
		case ir.Struct:
			return d.Symbol
		default:
			return ir.Symbol{}
		}
	}
	for _, decl := range pkg.Decls {
		id := symbol(decl)
		if id.Name == "" {
			continue
		}
		decls[id] = decl
		order = append(order, id)
		var fields []ir.Field
		switch d := decl.(type) {
		case ir.Enum:
			fields = d.Variants
		case ir.Struct:
			fields = d.Fields
		}
		for _, f := range fields {
			edges[id] = append(edges[id], typeEdges(f.Type, true)...)
		}
	}
	// Tarjan's algorithm for strongly connected components.
	index := make(map[ir.Symbol]int)
	component := make(map[ir.Symbol]int)
	active := make(map[ir.Symbol]bool)
	var stack []ir.Symbol
	var groups [][]ir.Symbol
	serial := 0
	var visit func(ir.Symbol) int
	visit = func(id ir.Symbol) int {
		serial++
		index[id] = serial
		low := serial
		stack = append(stack, id)
		active[id] = true
		for _, edge := range edges[id] {
			to := edge.target
			if decls[to] == nil {
				continue
			}
			if index[to] == 0 {
				low = min(low, visit(to))
			} else if active[to] {
				low = min(low, index[to])
			}
		}
		if low == index[id] {
			var group []ir.Symbol
			for {
				last := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				active[last] = false
				component[last] = len(groups)
				group = append(group, last)
				if last == id {
					break
				}
			}
			groups = append(groups, group)
		}
		return low
	}
	for _, id := range order {
		if index[id] == 0 {
			visit(id)
		}
	}
	for i, group := range groups {
		hasEnum := false
		recursive := len(group) > 1
		for _, id := range group {
			if _, ok := decls[id].(ir.Enum); ok {
				hasEnum = true
			}
			for _, edge := range edges[id] {
				if decls[edge.target] == nil || component[edge.target] != i {
					continue
				}
				recursive = true
				if !edge.supported {
					return fmt.Errorf("%s: recursive type edge %s -> %s through unsupported container", pkg.Path, id.Name, edge.target.Name)
				}
			}
		}
		if recursive && !hasEnum {
			record, ok := decls[group[0]].(ir.Struct)
			if len(group) != 1 || !ok || !record.Recursive {
				return fmt.Errorf("%s: recursive record %s", pkg.Path, group[0].Name)
			}
		}
	}
	var result []ir.Declaration
	emitted := make(map[int]bool)
	var emit func(int)
	emit = func(i int) {
		if emitted[i] {
			return
		}
		emitted[i] = true
		group := groups[i]
		var types []ir.Declaration
		for _, id := range group {
			for _, edge := range edges[id] {
				if decls[edge.target] != nil {
					emit(component[edge.target])
				}
			}
			types = append(types, decls[id])
		}
		if len(types) > 1 {
			result = append(result, ir.Mutual{Types: types})
		} else {
			result = append(result, types[0])
		}
	}
	for _, decl := range pkg.Decls {
		if id := symbol(decl); id.Name != "" {
			emit(component[id])
		} else {
			result = append(result, decl)
		}
	}
	pkg.Decls = result
	return nil
}
