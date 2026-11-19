package transpile

import (
	"fmt"
	"go/types"
	"net/url"
	"os"
	"path/filepath"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/lean"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"github.com/pelletier/go-toml/v2"
	"golang.org/x/tools/go/ssa"
)

func verificationRoots(programs []gosource.Program) (map[*ssa.Function]gosource.Program, error) {
	owners := make(map[*ssa.Function]gosource.Program)
	for _, program := range programs {
		for _, fn := range program.Roots {
			owners[fn] = program
		}
	}
	for _, program := range programs {
		for _, fn := range program.Roots {
			names := make(map[string]bool)
			for _, target := range program.Directives[fn].Abstract {
				callee := target.Callee
				owner, exists := owners[callee]
				assumed := len(program.Assumptions[callee]) != 0
				name := functionName(callee)
				switch {
				case !scalarFunction(fn):
					return nil, fmt.Errorf("%s: abstraction requires a non-generic scalar caller", target.Position)
				case !scalarFunction(callee):
					return nil, fmt.Errorf("%s: abstract callee must take scalar arguments and return one scalar result; methods require a scalar value receiver", target.Position)
				case !assumed && (!exists || len(owner.Directives[callee].Laws) == 0):
					return nil, fmt.Errorf("%s: abstract callee %s requires named //golean:assume or //golean:verify laws in this Go module", target.Position, callee)
				case names[name]:
					return nil, fmt.Errorf("%s: abstract callees must use distinct function names", target.Position)
				case !hasDirectCall(fn, callee):
					return nil, fmt.Errorf("%s: %s must be called directly by %s", target.Position, callee, fn.Name())
				}
				names[name] = true
				if assumed {
					continue
				}
				for _, root := range owner.Roots {
					if (owner.Path != program.Path || root == callee) && len(owner.Directives[root].Abstract) != 0 {
						return nil, fmt.Errorf("%s: abstract callee must belong to a module with concrete proofs", target.Position)
					}
				}
			}
		}
	}
	return owners, nil
}

func scalarFunction(fn *ssa.Function) bool {
	sig := fn.Signature
	if sig.TypeParams().Len() != 0 || sig.RecvTypeParams().Len() != 0 || len(fn.TypeArgs()) != 0 || sig.Variadic() || sig.Results().Len() != 1 {
		return false
	}
	scalar := func(t types.Type) bool {
		switch kind := subset.Type(t); kind {
		case ir.Bool, ir.Float32, ir.Float64:
			return true
		default:
			return kind.IsInteger()
		}
	}
	if recv := sig.Recv(); recv != nil && !scalar(recv.Type()) {
		return false
	}
	for param := range sig.Params().Variables() {
		if !scalar(param.Type()) {
			return false
		}
	}
	return scalar(sig.Results().At(0).Type())
}

func hasDirectCall(caller, callee *ssa.Function) bool {
	for _, block := range caller.Blocks {
		for _, instruction := range block.Instrs {
			if call, ok := instruction.(*ssa.Call); ok && call.Call.StaticCallee() == callee {
				return true
			}
		}
	}
	return false
}

func rootSymbol(program gosource.Program, fn *ssa.Function) ir.Symbol {
	return ir.Symbol{Package: program.Package.Pkg.Path(), File: url.PathEscape(sourceStem(program.Path)), Name: functionName(fn)}
}

func functionName(fn *ssa.Function) string {
	name := fn.Name()
	if receiver := fn.Signature.Recv(); receiver != nil {
		t := types.Unalias(receiver.Type())
		if pointer, ok := t.(*types.Pointer); ok {
			t = types.Unalias(pointer.Elem())
		}
		name = t.(*types.Named).Obj().Name() + "$" + name
	}
	return name
}

func abstractSymbol(caller ir.Symbol, callee *ssa.Function) ir.Symbol {
	symbol := ir.Symbol{Package: caller.Package, File: caller.File, Name: functionName(callee)}
	if path := callee.Pkg.Pkg.Path(); path != caller.Package {
		symbol.Dependency = path
	}
	return symbol
}

func assumedSignature(fn *ssa.Function) ir.Function {
	sig := fn.Signature
	model := ir.Function{Result: subset.Type(sig.Results().At(0).Type())}
	if recv := sig.Recv(); recv != nil {
		model.Params = append(model.Params, ir.Binder{Type: subset.Type(recv.Type())})
	}
	for param := range sig.Params().Variables() {
		model.Params = append(model.Params, ir.Binder{Type: subset.Type(param.Type())})
	}
	return model
}

func findModel(program ir.Program, symbol ir.Symbol) (ir.Function, bool) {
	for _, fn := range program.Functions {
		if fn.Symbol == symbol {
			return fn, true
		}
	}
	return ir.Function{}, false
}

func makeVerification(dir string, program gosource.Program, owners map[*ssa.Function]gosource.Program, lowered map[string]ir.Program) (lean.Verification, error) {
	var verification lean.Verification
	for _, fn := range program.Roots {
		directives := program.Directives[fn]
		if len(directives.Laws) == 0 {
			continue
		}
		symbol := rootSymbol(program, fn)
		model, found := findModel(lowered[program.Path], symbol)
		if !found {
			return verification, fmt.Errorf("%s: no Lean model for %s", directives.Laws[0].Position, fn)
		}
		root := lean.VerificationRoot{Symbol: symbol, Laws: directives.Laws}
		for _, target := range directives.Abstract {
			if model.Loop != nil || model.Fuel != nil {
				return verification, fmt.Errorf("%s: abstraction is unsupported in a loop helper or fuelled caller", target.Position)
			}
			if laws := program.Assumptions[target.Callee]; len(laws) != 0 {
				root.Abstract = append(root.Abstract, lean.AbstractCall{
					Call: abstractSymbol(symbol, target.Callee), Signature: assumedSignature(target.Callee), Operation: target.Callee.Name(), Laws: laws,
				})
				continue
			}
			owner := owners[target.Callee]
			callee := rootSymbol(owner, target.Callee)
			concrete, found := findModel(lowered[owner.Path], callee)
			if !found || concrete.CanPanic || len(concrete.Contracts) != 0 {
				return verification, fmt.Errorf("%s: abstract callee %s must have a total concrete model", target.Position, target.Callee)
			}
			module, err := leanModule(dir, owner.Path)
			if err != nil {
				return verification, err
			}
			root.Abstract = append(root.Abstract, lean.AbstractCall{
				Call: abstractSymbol(symbol, target.Callee), Signature: concrete, Operation: callee.Name, Module: module, Laws: owner.Directives[target.Callee].Laws,
			})
		}
		verification.Roots = append(verification.Roots, root)
	}
	if len(verification.Roots) == 0 {
		return verification, nil
	}
	module, err := leanModule(dir, program.Path)
	verification.Module = module
	return verification, err
}

// leanModule uses the most specific configured Lake source directory.
func leanModule(dir, file string) (string, error) {
	type library struct{ SrcDir string }
	var config struct {
		SrcDir    string
		Libraries []library `toml:"lean_lib"`
	}
	configPath := filepath.Join(dir, "lakefile.toml")
	data, err := os.ReadFile(configPath)
	if err == nil {
		if err := toml.Unmarshal(data, &config); err != nil {
			return "", fmt.Errorf("%s: %w", configPath, err)
		}
	} else if !os.IsNotExist(err) {
		return "", err
	}
	projectRoot, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	packageRoot := filepath.Join(projectRoot, config.SrcDir)
	sourceRoot := packageRoot
	for _, lib := range config.Libraries {
		candidate := filepath.Join(packageRoot, lib.SrcDir)
		rel, err := filepath.Rel(candidate, file)
		if err == nil && filepath.IsLocal(rel) && len(candidate) > len(sourceRoot) {
			sourceRoot = candidate
		}
	}
	relative, err := filepath.Rel(sourceRoot, file)
	if err != nil || !filepath.IsLocal(relative) {
		return "", fmt.Errorf("%s: cannot determine Lean module relative to %s", file, sourceRoot)
	}
	module := filepath.ToSlash(strings.TrimSuffix(relative, ".go"))
	if strings.ContainsAny(module, "«»\n\r") {
		return "", fmt.Errorf("%s: unsupported Lean module path", file)
	}
	return module, nil
}
