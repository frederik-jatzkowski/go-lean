package lower

import (
	"fmt"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type typeEdge struct {
	target    ir.Symbol
	supported bool
}

func typeEdges(t ir.Type, direct bool) []typeEdge {
	switch t := t.Case().(type) {
	case ir.RecordType:
		return []typeEdge{{target: t.Symbol, supported: direct}}
	case ir.EnumTypeRef:
		return []typeEdge{{target: t.Symbol, supported: direct}}
	case ir.BoxType:
		kind := t.Element.Kind()
		return typeEdges(t.Element, direct && (kind == ir.Record || kind == ir.EnumType))
	case ir.ArrayType:
		return typeEdges(t.Element, false)
	case ir.OptionType:
		return typeEdges(t.Element, false)
	case ir.ListType:
		return typeEdges(t.Element, false)
	case ir.FoldControlType:
		return typeEdges(t.Element, false)
	case ir.MapType:
		return append(typeEdges(t.Value, false), typeEdges(t.Key, false)...)
	case ir.SetType:
		return typeEdges(t.Key, false)
	default:
		return nil
	}
}

// Group recursive type declarations while keeping ordinary declaration order.
// A group can pull in a type dependency that originally followed its first member.
func groupTypes(pkg *packageBuilder) error {
	decls := make(map[ir.Symbol]ir.Declaration)
	edges := make(map[ir.Symbol][]typeEdge)
	var order []ir.Symbol
	symbol := func(decl ir.Declaration) ir.Symbol {
		switch d := decl.Case().(type) {
		case ir.Enum:
			return d.Symbol
		case ir.Struct:
			return d.Symbol
		default:
			return ir.Symbol{}
		}
	}
	for _, decl := range pkg.decls {
		id := symbol(decl)
		if id.Name == "" {
			continue
		}
		decls[id] = decl
		order = append(order, id)
		var fields lean.List[ir.Field]
		switch d := decl.Case().(type) {
		case ir.Enum:
			fields = d.Variants
		case ir.Struct:
			fields = d.Fields
		}
		edges[id] = lean.FoldList(fields, nil, appendTypeEdges)
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
			if _, exists := decls[to]; !exists {
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
			if _, ok := decls[id].Case().(ir.Enum); ok {
				hasEnum = true
			}
			for _, edge := range edges[id] {
				if _, exists := decls[edge.target]; !exists || component[edge.target] != i {
					continue
				}
				recursive = true
				if !edge.supported {
					return fmt.Errorf("%s: recursive type edge %s -> %s through unsupported container", pkg.Path, id.Name, edge.target.Name)
				}
			}
		}
		if recursive && !hasEnum {
			record, ok := decls[group[0]].Case().(ir.Struct)
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
		for _, id := range group {
			for _, edge := range edges[id] {
				if _, exists := decls[edge.target]; exists {
					emit(component[edge.target])
				}
			}
		}
		if len(group) == 1 {
			result = append(result, decls[group[0]])
			return
		}
		members := make([]ir.MutualMember, 0, len(group))
		for _, id := range group {
			switch decl := decls[id].Case().(type) {
			case ir.Struct:
				members = append(members, ir.NewMutualMemberMutualRecord(ir.MutualRecord{Record: decl}))
			case ir.Enum:
				members = append(members, ir.NewMutualMemberMutualEnum(ir.MutualEnum{Enum: decl}))
			}
		}
		result = append(result, ir.NewDeclarationMutual(ir.Mutual{Types: list(members)}))
	}
	for _, decl := range pkg.decls {
		if id := symbol(decl); id.Name != "" {
			emit(component[id])
		} else {
			result = append(result, decl)
		}
	}
	pkg.decls = result
	return nil
}

func appendTypeEdges(field ir.Field, edges []typeEdge) []typeEdge {
	return append(edges, typeEdges(field.Type, true)...)
}
