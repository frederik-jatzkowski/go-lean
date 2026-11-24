// Package load indexes build-selected Go declarations and go-lean directives.
package load

import (
	"context"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"
	"strings"
	"unicode"

	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/internal/enums"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
	"golang.org/x/tools/go/packages"
)

func Read(ctx context.Context, dir, pattern string) (loaded.Program, error) {
	if err := enums.Process(ctx, dir, pattern, false); err != nil {
		return loaded.Program{}, err
	}
	cfg := &packages.Config{Context: ctx, Dir: dir, Mode: packages.LoadAllSyntax | packages.NeedModule}
	roots, err := packages.Load(cfg, pattern)
	if err != nil {
		return loaded.Program{}, err
	}
	var diagnostics []string
	packages.Visit(roots, nil, func(p *packages.Package) {
		for _, issue := range p.Errors {
			diagnostics = append(diagnostics, issue.Error())
		}
	})
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return loaded.Program{}, fmt.Errorf("%s", strings.Join(slices.Compact(diagnostics), "\n"))
	}
	return build(roots)
}

func directive(text string) (kind, value string, ok bool) {
	text, ok = strings.CutPrefix(text, "//golean:")
	kind = strings.TrimSpace(text)
	if i := strings.IndexFunc(kind, unicode.IsSpace); i >= 0 {
		kind, value = kind[:i], strings.TrimSpace(kind[i:])
	}
	return kind, value, ok
}

func proposition(value string) (loaded.Proposition, bool) {
	name, lean, ok := strings.Cut(value, ":")
	name, lean = strings.TrimSpace(name), strings.TrimSpace(lean)
	return loaded.Proposition{Name: name, Lean: lean}, ok && token.IsIdentifier(name) && name != "_" && lean != ""
}

func validModule(value string) bool {
	for part := range strings.SplitSeq(value, ".") {
		if !token.IsIdentifier(part) || part == "_" {
			return false
		}
	}
	return true
}

func readPackageDirectives(p *packages.Package, doc *ast.CommentGroup, laws []loaded.Proposition, imports []string) ([]loaded.Proposition, []string, string) {
	if doc == nil {
		return laws, imports, ""
	}
	initialLaws := laws
	var previous *loaded.Proposition
	for _, comment := range doc.List {
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
		}
		fail := func(message string, args ...any) ([]loaded.Proposition, []string, string) {
			return initialLaws, imports, sourceError(p, comment.Pos(), message, args...)
		}
		switch kind {
		case "generate:enum":
			previous = nil
		case "verify":
			law, valid := proposition(value)
			if !valid {
				return fail("expected golean:verify name : proposition")
			}
			for _, existing := range laws {
				if existing.Name == law.Name {
					return fail("duplicate package law %s", law.Name)
				}
			}
			laws = append(laws, law)
			previous = &laws[len(laws)-1]
		case "verify+":
			if previous == nil || value == "" {
				return fail("unexpected golean:verify+ continuation")
			}
			previous.Lean += "\n" + value
		case "verify:import":
			previous = nil
			if !validModule(value) {
				return fail("expected golean:verify:import Lean.Module")
			}
			imports = append(imports, value)
		default:
			return fail("unsupported package golean:%s directive", kind)
		}
	}
	return laws, imports, ""
}

func firstDirective(groups ...*ast.CommentGroup) token.Pos {
	for _, group := range groups {
		if group == nil {
			continue
		}
		for _, comment := range group.List {
			if strings.HasPrefix(comment.Text, "//golean:") {
				return comment.Pos()
			}
		}
	}
	return token.NoPos
}

func packageDir(p *packages.Package) string {
	if len(p.GoFiles) != 0 {
		return filepath.Dir(p.GoFiles[0])
	}
	return p.Dir
}

func sourceError(p *packages.Package, pos token.Pos, message string, args ...any) string {
	return fmt.Sprintf("%s: %s", p.Fset.Position(pos), fmt.Sprintf(message, args...))
}

func readDirectives(p *packages.Package, file *ast.File, decl *ast.FuncDecl, objectID func(types.Object) loaded.ObjectID) loaded.Function {
	f := loaded.Function{Pos: p.Fset.Position(decl.Pos()).String()}
	if decl.Doc == nil {
		return f
	}
	var laws, assumptions []loaded.Proposition
	var positions []string
	var abstract []loaded.AbstractCallee
	var previous *loaded.Proposition
	var continuation string
	for _, comment := range decl.Doc.List {
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
		}
		if kind == "verify" || kind == "export" || strings.HasPrefix(kind, "verify") || kind == "abstract" {
			f.Selected = true
		}
		fail := func(format string, args ...any) {
			if f.Issue == "" {
				f.Issue = sourceError(p, comment.Pos(), format, args...)
			}
		}
		if kind == "verify+" || kind == "assume+" {
			if previous == nil || continuation != kind || value == "" {
				fail("unexpected golean:%s continuation", kind)
			} else {
				previous.Lean += "\n" + value
			}
			continue
		}
		previous = nil
		switch kind {
		case "export":
			if f.Export || value != "" {
				fail("expected one bare golean:export")
			}
			f.Export = true
		case "termination:by":
			if value == "" || f.Termination != "" {
				fail("expected one nonempty golean:termination:by measure")
			}
			f.Termination = value
		case "abstract":
			if value == "" || slices.ContainsFunc(abstract, func(target loaded.AbstractCallee) bool { return target.Name == value }) {
				fail("expected a unique golean:abstract callee")
			}
			target := resolveCallee(p, file, value)
			var id loaded.ObjectID
			if target != nil {
				id = objectID(target)
			}
			abstract = append(abstract, loaded.AbstractCallee{Name: value, Object: id})
		case "assume", "verify":
			law, ok := proposition(value)
			if !ok {
				fail("expected golean:%s name : proposition", kind)
				continue
			}
			list := &laws
			if kind == "assume" {
				list = &assumptions
			} else {
				positions = append(positions, p.Fset.Position(comment.Pos()).String())
			}
			for _, existing := range *list {
				if existing.Name == law.Name {
					fail("duplicate golean:%s law %s", kind, law.Name)
				}
			}
			*list = append(*list, law)
			previous, continuation = &(*list)[len(*list)-1], kind+"+"
		default:
			fail("unsupported golean:%s directive", kind)
		}
	}
	f.Laws = lean.ArrayFromSlice(laws)
	f.Assumptions = lean.ArrayFromSlice(assumptions)
	f.LawPositions = lean.ArrayFromSlice(positions)
	f.Abstract = lean.ArrayFromSlice(abstract)
	return f
}

// resolveCallee resolves a local or file-import-qualified function name.
func resolveCallee(p *packages.Package, file *ast.File, name string) *types.Func {
	qualifier, member, qualified := strings.Cut(name, ".")
	if !qualified {
		fn, _ := p.Types.Scope().Lookup(name).(*types.Func)
		return fn
	}
	for _, spec := range file.Imports {
		var imported *types.PkgName
		if spec.Name == nil {
			imported, _ = p.TypesInfo.Implicits[spec].(*types.PkgName)
		} else {
			imported, _ = p.TypesInfo.Defs[spec.Name].(*types.PkgName)
		}
		if imported != nil && imported.Name() == qualifier {
			fn, _ := imported.Imported().Scope().Lookup(member).(*types.Func)
			return fn
		}
	}
	return nil
}
