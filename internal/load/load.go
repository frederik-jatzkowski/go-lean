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
	Termination       string
	Laws, Assumptions []ir.Proposition
	LawPositions      []token.Pos
	Abstract          []string
	Err               error
	Selected          bool
}

type Declaration struct {
	Pos    token.Pos
	Object types.Object
}

type Program struct {
	SelectedPackages []string
	// Declarations has an entry for every modeled package, including law-only packages.
	Declarations  map[string][]Declaration
	PackageLaws   map[string][]ir.Proposition
	LeanImports   map[string][]string
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
		Declarations:  make(map[string][]Declaration),
		PackageLaws:   make(map[string][]ir.Proposition),
		LeanImports:   make(map[string][]string),
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
		var declarations []Declaration
		var marked bool
		files := slices.Clone(p.Syntax)
		slices.SortFunc(files, func(a, b *ast.File) int {
			return strings.Compare(p.Fset.PositionFor(a.Pos(), false).Filename, p.Fset.PositionFor(b.Pos(), false).Filename)
		})
		for _, file := range files {
			program.readPackageDirectives(p, file.Doc)
			for _, decl := range file.Decls {
				switch d := decl.(type) {
				case *ast.GenDecl:
					for _, raw := range d.Specs {
						switch spec := raw.(type) {
						case *ast.TypeSpec:
							obj := p.TypesInfo.Defs[spec.Name].(*types.TypeName)
							if pos := firstDirective(d.Doc, spec.Doc); pos.IsValid() {
								program.TypeIssues[obj] = Error(p, pos, "type directives are unsupported; attach laws to functions")
							}
							declarations = append(declarations, Declaration{Pos: spec.Pos(), Object: obj})
						case *ast.ValueSpec:
							for _, name := range spec.Names {
								obj := p.TypesInfo.Defs[name]
								declarations = append(declarations, Declaration{Pos: name.Pos(), Object: obj})
							}
						}
					}
				case *ast.FuncDecl:
					object := p.TypesInfo.Defs[d.Name]
					declarations = append(declarations, Declaration{Pos: d.Pos(), Object: object})
					obj, ok := object.(*types.Func)
					if !ok {
						continue
					}
					entry := Function{Package: p, File: file, Decl: d}
					entry.readDirectives()
					program.Functions[obj] = entry
					marked = marked || entry.Selected
				}
			}
		}
		if p.PkgPath != Curated && (marked || len(program.PackageLaws[p.PkgPath]) != 0) {
			program.Declarations[p.PkgPath] = declarations
			if requested[p.ID] {
				program.SelectedPackages = append(program.SelectedPackages, p.PkgPath)
			}
		}
	})
	slices.Sort(program.SelectedPackages)
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

func directive(text string) (kind, value string, ok bool) {
	text, ok = strings.CutPrefix(text, "//golean:")
	kind = strings.TrimSpace(text)
	if i := strings.IndexFunc(kind, unicode.IsSpace); i >= 0 {
		kind, value = kind[:i], strings.TrimSpace(kind[i:])
	}
	return kind, value, ok
}

func proposition(value string) (ir.Proposition, bool) {
	name, lean, ok := strings.Cut(value, ":")
	name, lean = strings.TrimSpace(name), strings.TrimSpace(lean)
	return ir.Proposition{Name: name, Lean: lean}, ok && token.IsIdentifier(name) && name != "_" && lean != ""
}

func validModule(value string) bool {
	for part := range strings.SplitSeq(value, ".") {
		if !token.IsIdentifier(part) || part == "_" {
			return false
		}
	}
	return true
}

func (program *Program) readPackageDirectives(p *packages.Package, doc *ast.CommentGroup) {
	path := p.PkgPath
	if doc == nil || program.PackageIssues[path] != nil {
		return
	}
	laws := program.PackageLaws[path]
	var previous *ir.Proposition
	for _, comment := range doc.List {
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
		}
		fail := func(message string, args ...any) {
			program.PackageIssues[path] = Error(p, comment.Pos(), message, args...)
		}
		switch kind {
		case "verify":
			law, valid := proposition(value)
			if !valid {
				fail("expected golean:verify name : proposition")
				return
			}
			for _, existing := range laws {
				if existing.Name == law.Name {
					fail("duplicate package law %s", law.Name)
					return
				}
			}
			laws = append(laws, law)
			previous = &laws[len(laws)-1]
		case "verify+":
			if previous == nil || value == "" {
				fail("unexpected golean:verify+ continuation")
				return
			}
			previous.Lean += "\n" + value
		case "verify:import":
			previous = nil
			if !validModule(value) {
				fail("expected golean:verify:import Lean.Module")
				return
			}
			program.LeanImports[path] = append(program.LeanImports[path], value)
		default:
			fail("unsupported package golean:%s directive", kind)
			return
		}
	}
	program.PackageLaws[path] = laws
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
		kind, value, ok := directive(comment.Text)
		if !ok {
			previous = nil
			continue
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
		case "termination:by":
			if value == "" || f.Termination != "" {
				fail("expected one nonempty golean:termination:by measure")
			}
			f.Termination = value
		case "abstract":
			if value == "" || slices.Contains(f.Abstract, value) {
				fail("expected a unique golean:abstract callee")
			}
			f.Abstract = append(f.Abstract, value)
		case "assume", "verify":
			law, ok := proposition(value)
			if !ok {
				fail("expected golean:%s name : proposition", kind)
				continue
			}
			list := &f.Laws
			if kind == "assume" {
				list = &f.Assumptions
			} else {
				f.LawPositions = append(f.LawPositions, comment.Pos())
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
