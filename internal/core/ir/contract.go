package ir

import (
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type contractAssumptions struct {
	Source lean.Array[loaded.Proposition]
	Laws   lean.List[Proposition]
}

func prependContractAssumption(index uint, state contractAssumptions) contractAssumptions {
	prop := state.Source.Get(state.Source.Size() - 1 - index).UnwrapOr(loaded.Proposition{Name: "", Lean: ""})
	value := Proposition{Name: prop.Name, Lean: prop.Lean}
	return contractAssumptions{Source: state.Source, Laws: lean.Cons(value, state.Laws)}
}

func prependScalarParam(kind loaded.ScalarKind, result lean.List[Type]) lean.List[Type] {
	return lean.Cons(ScalarFromLoaded(kind), result)
}

func prependContractType(t Type, types lean.List[Type]) lean.List[Type] {
	return lean.Cons(t, types)
}

// ContractFromChecked constructs an IR contract from a checked signature.
//
//golean:export
func ContractFromChecked(caller Symbol, target Symbol, assumptions lean.Array[loaded.Proposition], checked loaded.CheckedContract) Contract {
	laws := lean.FoldN(assumptions.Size(), contractAssumptions{Source: assumptions, Laws: lean.List[Proposition]{}}, prependContractAssumption)
	reversed := lean.FoldList(checked.Params, lean.List[Type]{}, prependScalarParam)
	params := lean.FoldList(reversed, lean.List[Type]{}, prependContractType)
	return Contract{Caller: caller, Callee: target, Params: params, Result: ScalarFromLoaded(checked.Result), Assumptions: laws.Laws}
}
