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

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/packages"
)

const Curated = "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Function struct {
	Package           *packages.Package
	File              *ast.File
	Decl              *ast.FuncDecl
	Export            bool
	Laws, Assumptions []ir.Proposition
	Abstract          []string
	Err               error
	Selected          bool
}

type Program struct {
	Roots         []*types.Func
	Functions     map[*types.Func]Function
	Packages      map[string]*packages.Package
	PackageIssues map[string]error
	TypeIssues    map[*types.TypeName]error
}

func Read(ctx context.Context, dir, pattern string) (*Program, error) {
	cfg := &packages.Config{Context: ctx, Dir: dir, Mode: packages.LoadAllSyntax | packages.NeedModule}
	roots, err := packages.Load(cfg, pattern)
	if err != nil {
		return nil, err
	}
	var diagnostics []string
	packages.Visit(roots, nil, func(p *packages.Package) {
		for _, issue := range p.Errors {
			diagnostics = append(diagnostics, issue.Error())
		}
	})
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return nil, fmt.Errorf("%s", strings.Join(slices.Compact(diagnostics), "\n"))
	}
	program := &Program{
		Functions:     make(map[*types.Func]Function),
		Packages:      make(map[string]*packages.Package),
		PackageIssues: make(map[string]error),
		TypeIssues:    make(map[*types.TypeName]error),
	}
	requested := make(map[string]bool)
	for _, p := range roots {
		requested[p.ID] = true
	}
	packages.Visit(roots, nil, func(p *packages.Package) {
		program.Packages[p.PkgPath] = p
		for _, file := range p.Syntax {
			if pos := firstDirective(file.Doc); pos.IsValid() && program.PackageIssues[p.PkgPath] == nil {
				program.PackageIssues[p.PkgPath] = Error(p, pos, "package directives are unsupported; attach laws to functions")
			}
			for _, decl := range file.Decls {
				if d, ok := decl.(*ast.GenDecl); ok && d.Tok == token.TYPE {
					for _, raw := range d.Specs {
						spec := raw.(*ast.TypeSpec)
						if pos := firstDirective(d.Doc, spec.Doc); pos.IsValid() {
							if obj, ok := p.TypesInfo.Defs[spec.Name].(*types.TypeName); ok {
								program.TypeIssues[obj] = Error(p, pos, "type directives are unsupported; attach laws to functions")
							}
						}
					}
				}
				f, ok := decl.(*ast.FuncDecl)
				if !ok {
					continue
				}
				obj, ok := p.TypesInfo.Defs[f.Name].(*types.Func)
				if !ok {
					continue
				}
				entry := Function{Package: p, File: file, Decl: f}
				entry.readDirectives()
				program.Functions[obj] = entry
				if p.PkgPath != Curated && requested[p.ID] && entry.Selected {
					program.Roots = append(program.Roots, obj)
				}
			}
		}
	})
	slices.SortFunc(program.Roots, func(a, b *types.Func) int {
		return strings.Compare(a.FullName(), b.FullName())
	})
	for _, p := range roots {
		if issue := program.PackageIssues[p.PkgPath]; issue != nil {
			diagnostics = append(diagnostics, issue.Error())
		}
	}
	if len(diagnostics) != 0 {
		slices.Sort(diagnostics)
		return nil, fmt.Errorf("%s", diagnostics[0])
	}
	return program, nil
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

func Dir(p *packages.Package) string {
	if len(p.GoFiles) != 0 {
		return filepath.Dir(p.GoFiles[0])
	}
	return p.Dir
}

func Error(p *packages.Package, pos token.Pos, message string, args ...any) error {
	return fmt.Errorf("%s: %s", p.Fset.Position(pos), fmt.Sprintf(message, args...))
}

func (f *Function) readDirectives() {
	if f.Decl.Doc == nil {
		return
	}
	var previous *ir.Proposition
	var continuation string
	for _, comment := range f.Decl.Doc.List {
		text, ok := strings.CutPrefix(comment.Text, "//golean:")
		if !ok {
			previous = nil
			continue
		}
		kind, value := strings.TrimSpace(text), ""
		if i := strings.IndexFunc(kind, unicode.IsSpace); i >= 0 {
			kind, value = kind[:i], strings.TrimSpace(kind[i:])
		}
		if kind == "verify" || kind == "export" || strings.HasPrefix(kind, "verify") || kind == "abstract" {
			f.Selected = true
		}
		fail := func(format string, args ...any) {
			if f.Err == nil {
				f.Err = Error(f.Package, comment.Pos(), format, args...)
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
		case "abstract":
			if value == "" || slices.Contains(f.Abstract, value) {
				fail("expected a unique golean:abstract callee")
			}
			f.Abstract = append(f.Abstract, value)
		case "assume", "verify":
			name, proposition, ok := strings.Cut(value, ":")
			name, proposition = strings.TrimSpace(name), strings.TrimSpace(proposition)
			if !ok || !token.IsIdentifier(name) || name == "_" || proposition == "" {
				fail("expected golean:%s name : proposition", kind)
				continue
			}
			list := &f.Laws
			if kind == "assume" {
				list = &f.Assumptions
			}
			for _, existing := range *list {
				if existing.Name == name {
					fail("duplicate golean:%s law %s", kind, name)
				}
			}
			*list = append(*list, ir.Proposition{Name: name, Lean: proposition})
			previous, continuation = &(*list)[len(*list)-1], kind+"+"
		default:
			fail("unsupported golean:%s directive", kind)
		}
	}
}

// ResolveCallee resolves a local or file-import-qualified function name.
func (f Function) ResolveCallee(name string) *types.Func {
	qualifier, member, qualified := strings.Cut(name, ".")
	if !qualified {
		fn, _ := f.Package.Types.Scope().Lookup(name).(*types.Func)
		return fn
	}
	for _, spec := range f.File.Imports {
		var imported *types.PkgName
		if spec.Name == nil {
			imported, _ = f.Package.TypesInfo.Implicits[spec].(*types.PkgName)
		} else {
			imported, _ = f.Package.TypesInfo.Defs[spec.Name].(*types.PkgName)
		}
		if imported != nil && imported.Name() == qualifier {
			fn, _ := imported.Imported().Scope().Lookup(member).(*types.Func)
			return fn
		}
	}
	return nil
}
