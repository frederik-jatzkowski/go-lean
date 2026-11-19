package gosource

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"strings"
	"unicode/utf8"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
)

type Law struct {
	Name        string
	Proposition string
	Position    token.Position
}

type Abstract struct {
	Callee   *ssa.Function
	Position token.Position
}

type Directives struct {
	Constructor bool
	Laws        []Law
	Abstract    []Abstract
}

type selectedRoot struct {
	constructor bool
	fn          *types.Func
	marked      bool
	laws        []Law
	assumptions []Law
	abstract    []abstractTarget
}

type abstractTarget struct {
	fn       *types.Func
	position token.Position
}

func selectRoots(pkg *packages.Package, file *ast.File) ([]selectedRoot, error) {
	imports := make(map[string]*types.Package)
	for _, spec := range file.Imports {
		obj := pkg.TypesInfo.Implicits[spec]
		if spec.Name != nil {
			obj = pkg.TypesInfo.Defs[spec.Name]
		}
		if name, ok := obj.(*types.PkgName); ok {
			imports[name.Name()] = name.Imported()
		}
	}
	var roots []selectedRoot
	names := make(map[string]bool)
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Doc == nil {
			continue
		}
		var root selectedRoot
		marked := false
		var continuation *Law
		var continuationKind string
		assumptionNames := make(map[string]bool)
		for _, comment := range fn.Doc.List {
			position := pkg.Fset.PositionFor(comment.Pos(), false)
			line := comment.Text
			directive := strings.Fields(line)[0]
			remainder := strings.TrimPrefix(line, directive)
			payload := strings.TrimSpace(remainder)
			switch directive {
			case "//golean:verify:constructor":
				if payload != "" || root.constructor {
					return nil, directiveError(position, "expected a single //golean:verify:constructor without arguments")
				}
				root.constructor = true
				marked = true
			case "//golean:export":
				if payload != "" {
					return nil, directiveError(position, "expected //golean:export without arguments")
				}
				marked = true
			case "//golean:verify+", "//golean:assume+":
				kind := strings.TrimSuffix(directive, "+")
				if continuation == nil || continuationKind != kind || position.Line != continuation.Position.Line+strings.Count(continuation.Proposition, "\n")+1 || payload == "" {
					return nil, directiveError(position, "expected a nonempty continuation immediately after a named %s law", kind)
				}
				// Drop the separator and preserve Lean's indentation.
				_, separator := utf8.DecodeRuneInString(remainder)
				continuation.Proposition += "\n" + remainder[separator:]
				continue
			case "//golean:verify", "//golean:assume":
				laws, usedNames, label := &root.laws, names, "verification"
				if directive == "//golean:assume" {
					laws, usedNames, label = &root.assumptions, assumptionNames, "assumed"
				} else {
					marked = true
				}
				if payload != "" || directive == "//golean:assume" {
					name, proposition, _ := strings.Cut(payload, ":")
					name, proposition = strings.TrimSpace(name), strings.TrimSpace(proposition)
					if !token.IsIdentifier(name) || name == "_" || proposition == "" {
						return nil, directiveError(position, "expected %s <name> : <Lean proposition>", directive)
					}
					if usedNames[name] {
						return nil, directiveError(position, "duplicate %s law %q", label, name)
					}
					usedNames[name] = true
					*laws = append(*laws, Law{Name: name, Proposition: proposition, Position: position})
					continuation = &(*laws)[len(*laws)-1]
					continuationKind = directive
					continue
				}
			case "//golean:abstract":
				target := resolveAbstract(pkg.Types, imports, payload)
				if target == nil {
					return nil, directiveError(position, "expected //golean:abstract followed by a function or declared method (optionally import-qualified)")
				}
				for _, existing := range root.abstract {
					if existing.fn == target {
						return nil, directiveError(position, "duplicate abstract callee %s", payload)
					}
				}
				root.abstract = append(root.abstract, abstractTarget{fn: target, position: position})
			}
			continuation = nil
		}
		if len(root.abstract) != 0 && len(root.laws) == 0 {
			return nil, directiveError(root.abstract[0].position, "abstraction requires a caller with a named //golean:verify law")
		}
		if marked || len(root.assumptions) != 0 {
			if fn.Name.Name == "_" || (fn.Recv == nil && fn.Name.Name == "init") {
				return nil, directiveError(pkg.Fset.Position(fn.Pos()), "directives require a named function or concrete method")
			}
			root.fn = pkg.TypesInfo.Defs[fn.Name].(*types.Func)
			root.marked = marked
			roots = append(roots, root)
		}
	}
	return roots, nil
}

func resolveAbstract(pkg *types.Package, imports map[string]*types.Package, payload string) *types.Func {
	parts := strings.Split(payload, ".")
	for _, part := range parts {
		if !token.IsIdentifier(part) || part == "_" {
			return nil
		}
	}
	if len(parts) > 1 && imports[parts[0]] != nil {
		pkg = imports[parts[0]]
		parts = parts[1:]
		if !token.IsExported(parts[0]) || !token.IsExported(parts[len(parts)-1]) {
			return nil
		}
	}
	switch len(parts) {
	case 1:
		fn, _ := pkg.Scope().Lookup(parts[0]).(*types.Func)
		return fn
	case 2:
		obj, _ := pkg.Scope().Lookup(parts[0]).(*types.TypeName)
		if obj != nil {
			if named, ok := types.Unalias(obj.Type()).(*types.Named); ok {
				for method := range named.Methods() {
					if method.Name() == parts[1] {
						return method
					}
				}
			}
		}
	}
	return nil
}

func directiveError(position token.Position, format string, args ...any) error {
	return packages.Error{Pos: position.String(), Msg: fmt.Sprintf(format, args...)}
}
