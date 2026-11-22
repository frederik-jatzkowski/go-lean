package transpile

import (
	"fmt"
	"go/token"
	"go/types"
	"maps"
	"os"
	"path/filepath"
	"reflect"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/lean"
	"github.com/frederik-jatzkowski/go-lean/internal/lower"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

type packageModel struct {
	path         string
	module       string
	program      ir.Program
	input        gosource.Program
	dependencies []string
	imports      map[string]bool
	external     map[ir.Symbol]ir.Function
	verification lean.Verification
}

func packageModels(files []gosource.Program) (map[string]*packageModel, []*packageModel, map[string]ir.Program, error) {
	models := make(map[string]*packageModel)
	lowered := make(map[string]ir.Program)
	if len(files) == 0 {
		return models, nil, lowered, nil
	}
	for path, location := range files[0].Packages {
		models[path] = &packageModel{
			path: filepath.Join(location.Directory, location.Name), dependencies: location.Imports,
			imports: make(map[string]bool), external: make(map[ir.Symbol]ir.Function),
			program: ir.Program{
				WordBits: files[0].WordBits,
				Records:  make(map[ir.Type]ir.Record), Contracts: make(map[ir.Type]ir.Contract),
			},
			verification: lean.Verification{
				Scope: ir.Symbol{Package: path}, PackagePath: path, SeparateLaws: true,
				ModelImports: slices.Clone(files[0].LeanImports[path].Assume),
				Constructors: make(map[ir.Symbol]bool),
			},
		}
	}
	directives := make(map[*ssa.Function]gosource.Directives)
	for _, file := range files {
		maps.Copy(directives, file.Directives)
		model := models[file.Package.Pkg.Path()]
		if model.input.Package == nil {
			model.input = file
			model.input.Directives = directives
			model.input.Roots = nil
		}
		model.input.Roots = append(model.input.Roots, file.Roots...)
	}
	var ordered []*packageModel
	seen := make(map[string]bool)
	var visit func(string)
	visit = func(path string) {
		model := models[path]
		if model == nil || seen[path] {
			return
		}
		seen[path] = true
		for _, dependency := range model.dependencies {
			visit(dependency)
		}
		ordered = append(ordered, model)
	}
	for _, path := range slices.Sorted(maps.Keys(models)) {
		visit(path)
	}
	available := make(map[ir.Symbol]ir.Function)
	traced := make(map[ir.Symbol]bool)
	for _, model := range ordered {
		if len(model.input.Roots) == 0 {
			continue
		}
		if err := model.lower(available, traced); err != nil {
			return nil, nil, nil, err
		}
		for _, fn := range model.program.Functions {
			if !fn.Traced {
				available[fn.Symbol] = fn
			}
		}
		maps.Copy(traced, model.program.TracedRoots)
	}

	// Records and contract types may first be encountered in a caller, including
	// those from packages with no marked function. Their Go declaration still
	// determines which Lean module owns the definition.
	declaredRecords := make(map[string]bool)
	for _, model := range ordered {
		if model.hasDefinitions() {
			declaredRecords[model.verification.PackagePath] = true
		}
		for _, record := range model.program.Records {
			declaredRecords[record.Symbol.Package] = true
		}
	}
	for i := len(ordered) - 1; i >= 0; i-- {
		model := ordered[i]
		path := model.verification.PackagePath
		if declaredRecords[path] {
			lower.AddPackageRecords(&model.program, path, standaloneRecords(files[0].Packages[path].Types, models))
			for _, record := range model.program.Records {
				declaredRecords[record.Symbol.Package] = true
			}
		}
	}
	typeOwners := make(map[ir.Type]string)
	for _, model := range ordered {
		for typ, record := range model.program.Records {
			owner := models[record.Symbol.Package]
			if owner == nil {
				return nil, nil, nil, fmt.Errorf("%s: %s belongs to a Go package outside the Lake workspace", model.path, typ)
			}
			if previous, ok := owner.program.Records[typ]; ok && !reflect.DeepEqual(previous, record) {
				return nil, nil, nil, fmt.Errorf("%s: incompatible modeled fields for %s across Go packages", model.path, typ)
			}
			owner.program.Records[typ] = record
			typeOwners[typ] = record.Symbol.Package
			if owner != model {
				model.imports[record.Symbol.Package] = true
			}
		}
		for typ, contract := range model.program.Contracts {
			owner := models[contract.Symbol.Package]
			if owner == nil {
				return nil, nil, nil, fmt.Errorf("%s: %s belongs to a Go package outside the Lake workspace", model.path, typ)
			}
			if previous, ok := owner.program.Contracts[typ]; ok && !reflect.DeepEqual(previous, contract) {
				return nil, nil, nil, fmt.Errorf("%s: incompatible interface contract for %s across Go packages", model.path, typ)
			}
			owner.program.Contracts[typ] = contract
			typeOwners[typ] = contract.Symbol.Package
			if owner != model {
				model.imports[contract.Symbol.Package] = true
			}
		}
	}
	for _, model := range ordered {
		model.importTypeDependencies(models, typeOwners)
	}
	for _, file := range files {
		lowered[file.Path] = models[file.Package.Pkg.Path()].program
	}
	return models, ordered, lowered, nil
}

// Keep exported records available when a focused build sees only a subset of
// their callers. Contracts need directive validation and remain demand-driven.
func standaloneRecords(pkg *types.Package, models map[string]*packageModel) []types.Type {
	scope := pkg.Scope()
	var records []types.Type
	for _, name := range scope.Names() {
		obj, ok := scope.Lookup(name).(*types.TypeName)
		if ok && obj.Exported() && !obj.IsAlias() && subset.Type(obj.Type()).IsRecord() && standaloneRecordType(obj.Type(), models) {
			records = append(records, obj.Type())
		}
	}
	return records
}

func standaloneRecordType(typ types.Type, models map[string]*packageModel) bool {
	typ = types.Unalias(typ)
	switch underlying := typ.Underlying().(type) {
	case *types.Array:
		return standaloneRecordType(underlying.Elem(), models)
	case *types.Slice:
		return standaloneRecordType(underlying.Elem(), models)
	case *types.Struct:
		named, ok := typ.(*types.Named)
		if !ok || named.Obj().Pkg() == nil || models[named.Obj().Pkg().Path()] == nil {
			return false
		}
		for field := range underlying.Fields() {
			if !standaloneRecordType(field.Type(), models) {
				return false
			}
		}
		return true
	default:
		return subset.Type(typ) != ""
	}
}

func (m *packageModel) lower(available map[ir.Symbol]ir.Function, traced map[ir.Symbol]bool) error {
	checked, err := subset.Check(m.input)
	if err != nil {
		return err
	}
	abstract := make(map[ir.Symbol]map[ir.Symbol]bool)
	abstractSSA := make(map[*ssa.Function]map[*ssa.Function]bool)
	for _, fn := range m.input.Roots {
		for _, target := range m.input.Directives[fn].Abstract {
			symbol := rootSymbol(m.input, fn)
			if abstract[symbol] == nil {
				abstract[symbol] = make(map[ir.Symbol]bool)
				abstractSSA[fn] = make(map[*ssa.Function]bool)
			}
			abstract[symbol][abstractSymbol(symbol, target.Callee)] = true
			abstractSSA[fn][target.Callee] = true
		}
	}
	sites := make(map[ir.Symbol]token.Position)
	for _, fn := range checked.Functions() {
		owner := fn
		if origin := fn.Origin(); origin != nil {
			owner = origin
		}
		if owner.Pkg != m.input.Package {
			continue
		}
		for _, block := range fn.Blocks {
			for _, instruction := range block.Instrs {
				call, ok := instruction.(*ssa.Call)
				if !ok || subset.IsSliceClone(call) {
					continue
				}
				callees := []*ssa.Function{call.Call.StaticCallee()}
				for _, arg := range call.Call.Args {
					if callback, ok := arg.(*ssa.Function); ok {
						callees = append(callees, callback)
					}
				}
				for _, target := range callees {
					if target == nil || target.Pkg == nil || target.Pkg == m.input.Package || abstractSSA[fn][target] {
						continue
					}
					symbol := ir.Symbol{Package: target.Pkg.Pkg.Path(), Name: functionName(target)}
					imported, ok := available[symbol]
					if !ok {
						return fmt.Errorf("%s: missing canonical package model for %s; select its declaration with //golean:export", fn.Prog.Fset.Position(instruction.Pos()), target)
					}
					m.external[symbol] = imported
					m.imports[symbol.Package] = true
					if _, exists := sites[symbol]; !exists {
						sites[symbol] = fn.Prog.Fset.Position(call.Pos())
					}
				}
			}
		}
	}
	var incompatible ir.Symbol
	m.program, incompatible = lower.FromPackageSSA(lower.NewInput(checked), checked.Groups(), m.input.WordBits, abstract, m.external)
	if incompatible != (ir.Symbol{}) {
		return fmt.Errorf("%s: Go call to %s.%s uses a different slice representation than its canonical package model (nil or capacity is modeled differently)", sites[incompatible], incompatible.Package, incompatible.Name)
	}
	m.program.WordBits = m.input.WordBits
	for _, fn := range m.program.Functions {
		if fn.Decreases != "" && len(fn.Contracts) != 0 {
			return fmt.Errorf("%s: //golean:decreases on %s does not support interface contracts", m.path, fn.Symbol.Name)
		}
	}
	if err := traceVerificationRoots(m.input, &m.program, abstract, m.external); err != nil {
		return err
	}
	if m.program.TracedRoots == nil {
		m.program.TracedRoots = make(map[ir.Symbol]bool)
	}
	for symbol := range m.external {
		if traced[symbol] {
			m.program.TracedRoots[symbol] = true
		}
	}
	return nil
}

func (m *packageModel) importTypeDependencies(models map[string]*packageModel, owners map[ir.Type]string) {
	owner := m.verification.PackagePath
	var scan func(ir.Type)
	scan = func(typ ir.Type) {
		if typ == "" {
			return
		}
		if left, right := typ.ProductShape(); left != "" {
			scan(left)
			scan(right)
			return
		}
		if key, value := typ.MapShape(); key != "" {
			scan(key)
			scan(value)
			return
		}
		if input, output := typ.UnaryFunctionShape(); input != "" {
			scan(input)
			scan(output)
			return
		}
		elem, _ := typ.ArrayShape()
		for _, inner := range []ir.Type{elem, typ.OptionElem(), typ.Pointee(), typ.SliceElem(), typ.BufferElem()} {
			scan(inner)
		}
		if dependency := owners[typ]; dependency != "" && dependency != owner {
			pkg := models[dependency]
			if record, ok := pkg.program.Records[typ]; ok {
				m.program.Records[typ] = record
			}
			if contract, ok := pkg.program.Contracts[typ]; ok {
				m.program.Contracts[typ] = contract
			}
			m.imports[dependency] = true
		}
	}
	for _, record := range m.program.Records {
		if record.Symbol.Package == owner {
			for _, field := range record.Fields {
				scan(field.Type)
			}
			for _, handle := range record.Handles {
				scan(handle)
			}
		}
	}
	for _, contract := range m.program.Contracts {
		if contract.Symbol.Package == owner {
			for _, method := range contract.Methods {
				for _, parameter := range method.Params {
					scan(parameter)
				}
				scan(method.Result)
			}
		}
	}
}

func (m *packageModel) hasDefinitions() bool {
	return len(m.program.Functions)+len(m.program.Records)+len(m.program.Contracts) != 0
}

func (m *packageModel) visibleFunctions() []ir.Function {
	functions := slices.Clone(m.program.Functions)
	for _, imported := range m.external {
		functions = append(functions, imported)
	}
	return functions
}

func (m *packageModel) addVerification(file lean.Verification) {
	v := &m.verification
	v.Roots = append(v.Roots, file.Roots...)
	v.ModelImports = append(v.ModelImports, file.ModelImports...)
	maps.Copy(v.Constructors, file.Constructors)
}

func (m *packageModel) outputs(models map[string]*packageModel, module string) ([]Output, error) {
	v := m.verification
	for path := range m.imports {
		v.ModelImports = append(v.ModelImports, models[path].module)
	}
	slices.Sort(v.ModelImports)
	v.ModelImports = slices.Compact(v.ModelImports)
	var outputs []Output
	if slices.ContainsFunc(m.program.Functions, func(fn ir.Function) bool { return fn.Decreases != "" }) {
		if _, err := os.Stat(m.path + "_decreases_proofs.lean"); err == nil {
			v.DecreaseModule = lean.DecreaseModule(module)
			v.DecreaseProofModule = lean.DecreaseProofModule(module)
			outputs = append(outputs, Output{Path: m.path + "_decreases.lean", Source: lean.RenderDecreases(m.program, v)})
		} else if !os.IsNotExist(err) {
			return nil, err
		}
	}
	return append(outputs, Output{Path: m.path + "_model.lean", Source: lean.RenderVerification(m.program, v)}), nil
}
