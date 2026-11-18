// Package gosource discovers verification roots and builds Go SSA.
package gosource

import (
	"cmp"
	"go/ast"
	"go/token"
	"go/types"
	"path/filepath"
	"slices"
	"strings"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

type Program struct {
	Path     string
	Package  *ssa.Package
	Roots    []*ssa.Function
	WordBits int64
}

type selectedFile struct {
	path  string
	pkg   *packages.Package
	roots []*types.Func
}

// Load finds marked functions in ./... and groups them by their source file.
func Load(dir string) ([]Program, error) {
	fset := token.NewFileSet()
	cfg := &packages.Config{Mode: packages.LoadAllSyntax, Dir: dir, Fset: fset}
	loaded, err := packages.Load(cfg, "./...")
	if err != nil {
		return nil, err
	}
	var loadErr error
	packages.Visit(loaded, func(p *packages.Package) bool {
		if loadErr == nil && len(p.Errors) > 0 {
			loadErr = p.Errors[0]
		}
		return loadErr == nil
	}, nil)
	if loadErr != nil {
		return nil, loadErr
	}

	var selected []selectedFile
	var selectedPackages []*packages.Package
	for _, pkg := range loaded {
		before := len(selected)
		for _, file := range pkg.Syntax {
			path := fset.PositionFor(file.Pos(), false).Filename
			// Compiled syntax can also contain synthetic files produced by cgo.
			if !slices.Contains(pkg.GoFiles, path) {
				continue
			}
			roots, err := selectRoots(pkg, file)
			if err != nil {
				return nil, err
			}
			if len(roots) != 0 {
				selected = append(selected, selectedFile{path: path, pkg: pkg, roots: roots})
			}
		}
		if len(selected) > before {
			selectedPackages = append(selectedPackages, pkg)
		}
	}
	if len(selected) == 0 {
		return nil, nil
	}
	slices.SortFunc(selected, func(a, b selectedFile) int { return cmp.Compare(a.path, b.path) })

	prog, _ := ssautil.AllPackages(selectedPackages, ssa.InstantiateGenerics)
	prog.Build()
	programs := make([]Program, 0, len(selected))
	for _, file := range selected {
		result := Program{
			Path: filepath.Clean(file.path), Package: prog.Package(file.pkg.Types),
			WordBits: 8 * file.pkg.TypesSizes.Sizeof(types.Typ[types.Int]),
		}
		for _, root := range file.roots {
			fn := prog.FuncValue(root)
			if fn == nil {
				return nil, packages.Error{Pos: fset.Position(root.Pos()).String(), Msg: "no SSA definition for " + root.Name()}
			}
			result.Roots = append(result.Roots, fn)
		}
		programs = append(programs, result)
	}
	return programs, nil
}

func selectRoots(pkg *packages.Package, file *ast.File) ([]*types.Func, error) {
	var roots []*types.Func
	for _, decl := range file.Decls {
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || !marked(fn.Doc) {
			continue
		}
		if fn.Recv != nil || fn.Name.Name == "_" || fn.Name.Name == "init" {
			return nil, packages.Error{Pos: pkg.Fset.Position(fn.Pos()).String(), Msg: "verification requires a named top-level function"}
		}
		roots = append(roots, pkg.TypesInfo.Defs[fn.Name].(*types.Func))
	}
	return roots, nil
}

func marked(doc *ast.CommentGroup) bool {
	if doc != nil {
		for _, comment := range doc.List {
			if strings.TrimSpace(comment.Text) == "//golean:verify" {
				return true
			}
		}
	}
	return false
}
