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
	ScopedLaws        []Law
	LeanImports       map[string]LeanImports
	Package           *ssa.Package
	Roots             []*ssa.Function
	Directives        map[*ssa.Function]Directives
	Assumptions       map[*ssa.Function][]Law
	WordBits          int64
	InterfaceDocs     map[*types.TypeName]InterfaceDoc
	InitializedFields map[*types.Var]bool
	Packages          map[string]PackageLocation
	Exports           map[*types.Func]bool
}

type PackageLocation struct {
	Directory string
	Name      string
	Imports   []string
	Types     *types.Package
}

type selectedFile struct {
	path  string
	pkg   *packages.Package
	roots []selectedRoot
	laws  []Law
}

// Load finds marked functions in ./... and groups them by their source file.
func Load(dir string) ([]Program, error) {
	return load(dir, "./...", nil)
}

// LoadWithFiles also reports the active Go files, including files without directives.
func LoadWithFiles(dir, pattern string) ([]Program, map[string]bool, error) {
	active := make(map[string]bool)
	programs, err := load(dir, pattern, active)
	return programs, active, err
}

func load(dir, pattern string, active map[string]bool) ([]Program, error) {
	fset := token.NewFileSet()
	cfg := &packages.Config{Mode: packages.LoadAllSyntax | packages.NeedModule, Dir: dir, Fset: fset}
	loaded, err := packages.Load(cfg, pattern)
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

	imports, err := packageLeanImports(loaded)
	if err != nil {
		return nil, err
	}
	var selected []selectedFile
	var selectedPackages []*packages.Package
	locations := make(map[string]PackageLocation)
	exports := make(map[*types.Func]bool)
	var workspace []*packages.Package
	explicit := make(map[*packages.Package]bool)
	for _, pkg := range loaded {
		explicit[pkg] = true
	}
	packages.Visit(loaded, func(pkg *packages.Package) bool {
		if explicit[pkg] || pkg.Module != nil && pkg.Module.Main {
			workspace = append(workspace, pkg)
		}
		return true
	}, nil)
	for _, pkg := range workspace {
		var dependencies []string
		for _, dep := range pkg.Imports {
			dependencies = append(dependencies, dep.PkgPath)
		}
		slices.Sort(dependencies)
		before := len(selected)
		for _, file := range pkg.Syntax {
			path := fset.PositionFor(file.Pos(), false).Filename
			// Compiled syntax can also contain synthetic files produced by cgo.
			if !slices.Contains(pkg.GoFiles, path) {
				continue
			}
			if active != nil {
				active[filepath.Clean(path)] = true
			}
			locations[pkg.PkgPath] = PackageLocation{Directory: filepath.Dir(path), Name: pkg.Name, Imports: dependencies, Types: pkg.Types}
			roots, err := selectRoots(pkg, file)
			if err != nil {
				return nil, err
			}
			for _, root := range roots {
				if root.exported {
					exports[root.fn] = true
				}
			}
			laws, err := scopedLaws(pkg, file, roots)
			if err != nil {
				return nil, err
			}
			if len(roots) != 0 || len(laws) != 0 {
				selected = append(selected, selectedFile{path: path, pkg: pkg, roots: roots, laws: laws})
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
			ScopedLaws:        file.laws,
			LeanImports:       imports,
			InterfaceDocs:     docs,
			InitializedFields: fields,
			Packages:          locations,
			Exports:           exports,
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
		if len(result.Roots) != 0 || len(result.ScopedLaws) != 0 {
			programs = append(programs, result)
		}
	}
	return programs, nil
}
