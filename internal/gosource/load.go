// Package gosource discovers verification roots and builds Go SSA.
package gosource

import (
	"cmp"

	"go/token"
	"go/types"
	"path/filepath"
	"slices"

	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

type Program struct {
	Path              string
	Package           *ssa.Package
	Roots             []*ssa.Function
	Directives        map[*ssa.Function]Directives
	Assumptions       map[*ssa.Function][]Law
	WordBits          int64
	InterfaceDocs     map[*types.TypeName]InterfaceDoc
	InitializedFields map[*types.Var]bool
}

type selectedFile struct {
	path  string
	pkg   *packages.Package
	roots []selectedRoot
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
	docs := interfaceDocs(loaded)
	fields := initializedFields(loaded)
	assumptions := make(map[*ssa.Function][]Law)
	programs := make([]Program, 0, len(selected))
	for _, file := range selected {
		result := Program{
			Path: filepath.Clean(file.path), Package: prog.Package(file.pkg.Types),
			InterfaceDocs:     docs,
			InitializedFields: fields,
			Assumptions:       assumptions,
			Directives:        make(map[*ssa.Function]Directives),
			WordBits:          8 * file.pkg.TypesSizes.Sizeof(types.Typ[types.Int]),
		}
		for _, root := range file.roots {
			fn := prog.FuncValue(root.fn)
			if fn == nil {
				return nil, packages.Error{Pos: fset.Position(root.fn.Pos()).String(), Msg: "no SSA definition for " + root.fn.Name()}
			}
			if len(root.assumptions) != 0 {
				assumptions[fn] = root.assumptions
			}
			if !root.marked {
				continue
			}
			result.Roots = append(result.Roots, fn)
			directives := Directives{Laws: root.laws, Constructor: root.constructor, InterfaceCalls: root.interfaceCalls}
			for _, target := range root.abstract {
				callee := prog.FuncValue(target.fn)
				if callee == nil {
					return nil, packages.Error{Pos: target.position.String(), Msg: "no SSA definition for " + target.fn.FullName()}
				}
				directives.Abstract = append(directives.Abstract, Abstract{Callee: callee, Position: target.position})
			}
			result.Directives[fn] = directives
		}
		if len(result.Roots) != 0 {
			programs = append(programs, result)
		}
	}
	return programs, nil
}
