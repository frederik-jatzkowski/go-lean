package lower

import (
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

func groupDeclarations(p *ir.Package, calls map[ir.Symbol][]ir.Symbol) {
	edges := make(map[ir.Symbol][]ir.Symbol)
	var visitType func(ir.Symbol, ir.Type)
	visitType = func(owner ir.Symbol, t ir.Type) {
		if t.Kind == ir.EnumType && t.Record.Package == p.Path {
			edges[owner] = append(edges[owner], t.Record)
		}
		if t.Element != nil {
			visitType(owner, *t.Element)
		}
		if t.Key != nil {
			visitType(owner, *t.Key)
		}
	}
	positions := make(map[ir.Symbol]int)
	for i, decl := range p.Decls {
		switch d := decl.(type) {
		case ir.Enum:
			positions[d.Symbol] = i
			for _, variant := range d.Variants {
				for _, field := range variant.Fields {
					visitType(d.Symbol, field.Type)
				}
			}
		case ir.Function:
			positions[d.Symbol] = i
			edges[d.Symbol] = calls[d.Symbol]
		}
	}

	index := make(map[ir.Symbol]int)
	low := make(map[ir.Symbol]int)
	visiting := make(map[ir.Symbol]bool)
	var stack []ir.Symbol
	var count int
	groups := make(map[int]ir.Mutual)
	claimed := make(map[int]bool)
	var visit func(ir.Symbol)
	visit = func(sym ir.Symbol) {
		count++
		index[sym], low[sym], visiting[sym] = count, count, true
		stack = append(stack, sym)
		for _, dependency := range edges[sym] {
			if _, local := positions[dependency]; !local {
				continue
			}
			if index[dependency] == 0 {
				visit(dependency)
				low[sym] = min(low[sym], low[dependency])
			} else if visiting[dependency] {
				low[sym] = min(low[sym], index[dependency])
			}
		}
		if low[sym] != index[sym] {
			return
		}
		var component []int
		for {
			last := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			visiting[last] = false
			component = append(component, positions[last])
			if last == sym {
				break
			}
		}
		if len(component) < 2 {
			return
		}
		slices.Sort(component)
		group := ir.Mutual{}
		for _, pos := range component {
			claimed[pos] = true
			group.Members = append(group.Members, p.Decls[pos])
		}
		groups[component[len(component)-1]] = group
	}
	for _, decl := range p.Decls {
		switch d := decl.(type) {
		case ir.Enum:
			if index[d.Symbol] == 0 {
				visit(d.Symbol)
			}
		case ir.Function:
			if index[d.Symbol] == 0 {
				visit(d.Symbol)
			}
		}
	}
	var ordered []ir.Declaration
	for i, decl := range p.Decls {
		if g, ok := groups[i]; ok {
			ordered = append(ordered, g)
		} else if !claimed[i] {
			ordered = append(ordered, decl)
		}
	}
	p.Decls = ordered
}
