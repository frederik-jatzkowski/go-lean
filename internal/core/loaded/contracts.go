package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// LocalContracts keeps track of which declared contracts a caller uses.
type LocalContracts struct {
	Uses lean.OrderedMap[ObjectID, bool]
}

type ContractUse struct {
	Contracts LocalContracts
	Found     bool
}

func (s LocalContracts) Has(id ObjectID) bool {
	return s.Uses.Contains(id)
}

// Declare schedules a checked contract for the caller.
//
//golean:export
func (s LocalContracts) Declare(id ObjectID) LocalContracts {
	return LocalContracts{Uses: s.Uses.Insert(id, false)}
}

// Use marks a caller-local contract if one was declared.
//
//golean:export
func (s LocalContracts) Use(id ObjectID) ContractUse {
	if !s.Has(id) {
		return ContractUse{Contracts: s, Found: false}
	}
	used := LocalContracts{Uses: s.Uses.Insert(id, true)}
	return ContractUse{Contracts: used, Found: true}
}

type ContractTarget struct {
	Source     Function
	Diagnostic Diagnostic
}

// CheckContractTarget validates one abstract target before constructing its
// signature. The source error takes precedence over duplicate resolution.
//
//golean:export
func (s LocalContracts) CheckContractTarget(from ObjectID, target AbstractCallee, object Object, pos string) ContractTarget {
	source := object.Function.UnwrapOr(emptyFunction())
	if target.Object == 0 || target.Object == from || source.Assumptions.Size() == 0 {
		issue := Diagnostic{Code: MissingContractAssumptions, Pos: pos, Detail: target.Name}
		return ContractTarget{Source: source, Diagnostic: issue}
	}
	if source.Issue != "" {
		issue := Diagnostic{Code: FunctionSourceIssue, Pos: "", Detail: source.Issue}
		return ContractTarget{Source: source, Diagnostic: issue}
	}
	if s.Has(target.Object) {
		issue := Diagnostic{Code: DuplicateContractTarget, Pos: pos, Detail: target.Name}
		return ContractTarget{Source: source, Diagnostic: issue}
	}
	return ContractTarget{Source: source, Diagnostic: validDiagnostic()}
}

type contractFinish struct {
	Contracts  LocalContracts
	Function   Function
	Diagnostic Diagnostic
}

func checkContractUse(index uint, state contractFinish) lean.FoldControl[contractFinish] {
	target := state.Function.Abstract.Get(index).UnwrapOr(AbstractCallee{Name: "", Object: 0})
	if !state.Contracts.Uses.Find(target.Object).UnwrapOr(false) {
		issue := Diagnostic{Code: UnusedContractTarget, Pos: state.Function.Pos, Detail: target.Name}
		next := contractFinish{Contracts: state.Contracts, Function: state.Function, Diagnostic: issue}
		return lean.FoldControl[contractFinish]{State: next, Stop: true}
	}
	return lean.FoldControl[contractFinish]{State: state, Stop: false}
}

// CheckFunctionFinish verifies body-dependent recursion and contract usage.
//
//golean:export
func (s LocalContracts) CheckFunctionFinish(source Function, recursive bool) Diagnostic {
	if source.Termination != "" && !recursive {
		return Diagnostic{Code: MissingMeasuredSelfCall, Pos: source.Pos, Detail: ""}
	}
	initial := contractFinish{Contracts: s, Function: source, Diagnostic: validDiagnostic()}
	return lean.FoldNUntil(source.Abstract.Size(), initial, checkContractUse).State.Diagnostic
}
