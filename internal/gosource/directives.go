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
	Laws     []Law
	Abstract []Abstract
}

type selectedRoot struct {
	fn       *types.Func
	laws     []Law
	abstract []abstractTarget
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
		for _, comment := range fn.Doc.List {
			position := pkg.Fset.PositionFor(comment.Pos(), false)
			line := comment.Text
			directive := strings.Fields(line)[0]
			remainder := strings.TrimPrefix(line, directive)
			payload := strings.TrimSpace(remainder)
			switch directive {
			case "//golean:export":
				if payload != "" {
					return nil, directiveError(position, "expected //golean:export without arguments")
				}
				marked = true
			case "//golean:verify+":
				if continuation == nil || position.Line != continuation.Position.Line+strings.Count(continuation.Proposition, "\n")+1 || payload == "" {
					return nil, directiveError(position, "expected a nonempty continuation immediately after a named //golean:verify law")
				}
				// Drop the separator and preserve Lean's indentation.
				_, separator := utf8.DecodeRuneInString(remainder)
				continuation.Proposition += "\n" + remainder[separator:]
				continue
			case "//golean:verify":
				marked = true
				if payload != "" {
					name, proposition, _ := strings.Cut(payload, ":")
					name, proposition = strings.TrimSpace(name), strings.TrimSpace(proposition)
					if !token.IsIdentifier(name) || name == "_" || proposition == "" {
						return nil, directiveError(position, "expected //golean:verify <name> : <Lean proposition>")
					}
					if names[name] {
						return nil, directiveError(position, "duplicate verification law %q", name)
					}
					names[name] = true
					root.laws = append(root.laws, Law{Name: name, Proposition: proposition, Position: position})
					continuation = &root.laws[len(root.laws)-1]
					continue
				}
			case "//golean:abstract":
				alias, name, _ := strings.Cut(payload, ".")
				targetPkg := imports[alias]
				var target *types.Func
				if targetPkg != nil && token.IsIdentifier(alias) {
					target, _ = targetPkg.Scope().Lookup(name).(*types.Func)
				}
				if target == nil || !target.Exported() {
					return nil, directiveError(position, "expected //golean:abstract <importAlias>.<exportedFunction>")
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
		if marked {
			if fn.Name.Name == "_" || (fn.Recv == nil && fn.Name.Name == "init") {
				return nil, directiveError(pkg.Fset.Position(fn.Pos()), "verification requires a named function or concrete method")
			}
			root.fn = pkg.TypesInfo.Defs[fn.Name].(*types.Func)
			roots = append(roots, root)
		}
	}
	return roots, nil
}

func directiveError(position token.Position, format string, args ...any) error {
	return packages.Error{Pos: position.String(), Msg: fmt.Sprintf(format, args...)}
}
