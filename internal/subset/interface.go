package subset

import (
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

func isInterfaceValue(t types.Type) bool {
	_, typeParam := types.Unalias(t).(*types.TypeParam)
	return !typeParam && types.IsInterface(t)
}

func InterfaceHandle(t types.Type) ir.Type {
	if named, ok := types.Unalias(t).(*types.Named); ok && types.IsInterface(named) && named.Obj().Pkg() != nil {
		obj := named.Obj()
		if obj.Parent() == obj.Pkg().Scope() {
			return ir.Type("interface:" + obj.Pkg().Path() + "." + obj.Name())
		}
	}
	return ""
}

func (c Checked) InterfaceLaws(t types.Type) []string {
	return c.contracts[types.Unalias(t).(*types.Named).Obj()]
}

func (c *checker) checkInterface(fn *ssa.Function, pos token.Pos, t types.Type) error {
	if InterfaceHandle(t) == "" {
		return diagnostic(fn, pos, "requires a named interface with a golean contract")
	}
	named := types.Unalias(t).(*types.Named)
	if named.TypeParams().Len() != 0 {
		return diagnostic(fn, pos, "generic interface contracts are unsupported")
	}
	obj := named.Obj()
	if c.contracts[obj] != nil {
		return nil
	}
	laws, err := c.interfaceDocs[obj].Laws()
	if err != nil {
		return err
	}
	if len(laws) == 0 {
		return diagnostic(fn, pos, "interface %s requires a golean contract", t)
	}
	iface := named.Underlying().(*types.Interface)
	if iface.NumEmbeddeds() != 0 {
		return diagnostic(fn, pos, "embedded interfaces are unsupported in golean contracts")
	}
	for method := range iface.ExplicitMethods() {
		sig := method.Signature()
		if sig.Variadic() || sig.Results().Len() != 1 {
			return diagnostic(fn, method.Pos(), "interface contract methods require one result and no variadic arguments")
		}
		for param := range sig.Params().Variables() {
			if Type(param.Type()) == "" {
				return diagnostic(fn, param.Pos(), "interface contract method parameters require supported Go value types")
			}
		}
		result := sig.Results().At(0).Type()
		if !types.Identical(result, t) && (Type(result) == "" || Type(result).Pointee() != "") {
			return diagnostic(fn, method.Pos(), "interface contract methods must return a supported value or the same interface")
		}
	}
	c.contracts[obj] = laws
	return nil
}

func supportedHandle(value ssa.Value) bool {
	if InterfaceHandle(value.Type()) == "" {
		return false
	}
	switch value.(type) {
	case *ssa.Parameter, *ssa.Call, *ssa.Phi, *ssa.Extract:
		return true
	default:
		return false
	}
}

func (c *checker) checkInvoke(fn *ssa.Function, call *ssa.Call) error {
	receiver := call.Call.Value
	if err := c.checkInterface(fn, call.Pos(), receiver.Type()); err != nil {
		return err
	}
	if !supportedHandle(receiver) {
		return diagnostic(fn, call.Pos(), "interface method requires a supported non-nil handle")
	}
	for _, arg := range call.Call.Args {
		if !supportedValue(arg) {
			return diagnostic(fn, call.Pos(), "interface method requires supported value arguments")
		}
	}
	return nil
}
