package lean

import (
	"fmt"
	"maps"
	"slices"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

// RenderAliases keeps file-scoped Lean clients and proof companions working
// while every alias resolves to the declaration in the owning package model.
func RenderAliases(program ir.Program, verification Verification, modelModule string, functions []ir.Function) string {
	var out strings.Builder
	fmt.Fprintf(&out, "%s\nimport %s\n", GeneratedHeader, modelModule)
	if !verification.SeparateLaws && len(verification.Roots) != 0 {
		out.WriteString("import Lean.Elab.Command\n")
		out.WriteString(declareLaw)
	}
	out.WriteString("\nnamespace GoLean\n")
	aliases := make(map[string]map[string][]string)
	add := func(to, from, name string) {
		if aliases[to] == nil {
			aliases[to] = make(map[string][]string)
		}
		aliases[to][from] = append(aliases[to][from], name)
	}
	previousScope := func(symbol ir.Symbol) string {
		destination := verification.Scope
		if symbol.Package != destination.Package {
			destination.Dependency = symbol.Package
		}
		return symbolNamespace(destination)
	}
	for _, fn := range functions {
		to, from := previousScope(fn.Symbol), symbolNamespace(fn.Symbol)
		name := fn.Symbol.Name
		if !fn.Traced && program.TracedRoots[fn.Symbol] {
			name += "$untraced"
		}
		add(to, from, quoted(name))
		if fn.Loop != nil {
			add(to, from, quoted(fn.Loop.Symbol.Name))
		}
		if verification.Constructors[fn.Symbol] {
			add(to, from, quoted(fn.Symbol.Name+"$initialized"))
		}
	}
	for _, record := range program.Records {
		symbol := record.Symbol
		to, from, name := previousScope(symbol), symbolNamespace(symbol), quoted(symbol.Name)
		add(to, from, name)
		add(to+"."+name, from+"."+name, "mk")
		for _, field := range record.Fields {
			add(to+"."+name, from+"."+name, recordFieldName(field.Name))
		}
	}
	for _, contract := range program.Contracts {
		symbol := contract.Symbol
		to := previousScope(symbol) + ".InterfaceContracts"
		add(to, symbolNamespace(symbol)+".InterfaceContracts", quoted(symbol.Name))
	}
	for _, root := range verification.Roots {
		suffix := ".AbstractCalls." + quoted(root.Symbol.Name)
		for _, target := range root.Abstract {
			add(symbolScope(verification.Scope)+suffix, symbolScope(root.Symbol)+suffix, quoted(target.Call.Name))
		}
	}
	if program.WordBits != 0 {
		to := symbolScope(verification.Scope) + ".GoTypes"
		from := symbolScope(ir.Symbol{Package: verification.Scope.Package}) + ".GoTypes"
		for _, name := range []string{"Int", "UInt", "WordBits"} {
			add(to, from, name)
		}
	}
	for _, to := range slices.Sorted(maps.Keys(aliases)) {
		fmt.Fprintf(&out, "\nnamespace %s\n", to)
		for _, from := range slices.Sorted(maps.Keys(aliases[to])) {
			names := aliases[to][from]
			slices.Sort(names)
			fmt.Fprintf(&out, "export GoLean.%s (%s)\n", from, strings.Join(slices.Compact(names), " "))
		}
		fmt.Fprintf(&out, "end %s\n", to)
	}
	if !verification.SeparateLaws {
		for _, root := range verification.Roots {
			renderLaws(&out, root, verification.Scope)
		}
	}
	out.WriteString("\nend GoLean\n")
	return out.String()
}
