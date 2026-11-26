package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type FunctionState uint8

const (
	UnvisitedFunction FunctionState = iota
	ActiveFunction
	CompleteFunction
)

type CallGraph struct {
	States lean.OrderedMap[ObjectID, FunctionState]
}

func (g CallGraph) State(id ObjectID) FunctionState {
	return g.States.Find(id).UnwrapOr(UnvisitedFunction)
}

// Start marks a function as active during dependency traversal.
//
//golean:export
func (g CallGraph) Start(id ObjectID) CallGraph {
	return CallGraph{States: g.States.Insert(id, ActiveFunction)}
}

// Finish marks a function as fully compiled.
//
//golean:export
func (g CallGraph) Finish(id ObjectID) CallGraph {
	return CallGraph{States: g.States.Insert(id, CompleteFunction)}
}

type FunctionEntry struct {
	Done       bool
	Source     Function
	Diagnostic Diagnostic
}

func emptyFunction() Function {
	return Function{Body: lean.Array[StmtID]{}, HasBody: false, Export: false, Selected: false,
		Pos: "", Termination: "", Issue: "", Laws: lean.Array[Proposition]{},
		Assumptions: lean.Array[Proposition]{}, LawPositions: lean.Array[string]{}, Abstract: lean.Array[AbstractCallee]{}}
}

// FunctionEntry checks entry ordering before signature and body traversal.
//
//golean:export
func (g CallGraph) FunctionEntry(id ObjectID, target Object) FunctionEntry {
	source := target.Function.UnwrapOr(emptyFunction())
	if !target.Function.IsSome() {
		issue := Diagnostic{Code: MissingFunctionSource, Pos: "", Detail: target.FullName}
		return FunctionEntry{Done: false, Source: source, Diagnostic: issue}
	}
	state := g.State(id)
	if state == ActiveFunction {
		issue := Diagnostic{Code: ActiveFunctionEntry, Pos: source.Pos, Detail: target.Name}
		return FunctionEntry{Done: false, Source: source, Diagnostic: issue}
	}
	if state == CompleteFunction {
		return FunctionEntry{Done: true, Source: source, Diagnostic: validDiagnostic()}
	}
	if source.Issue != "" {
		issue := Diagnostic{Code: FunctionSourceIssue, Pos: "", Detail: source.Issue}
		return FunctionEntry{Done: false, Source: source, Diagnostic: issue}
	}
	return FunctionEntry{Done: false, Source: source, Diagnostic: validDiagnostic()}
}

// ValidateCallEdge checks the call graph after its export and dependency checks.
//
//golean:export
func (g CallGraph) ValidateCallEdge(id ObjectID, target Object, pos string) Diagnostic {
	if g.State(id) == ActiveFunction {
		return Diagnostic{Code: ActiveCallEdge, Pos: pos, Detail: target.FullName}
	}
	return validDiagnostic()
}

// ValidateFunctionContractMode checks the caller's directives after signature
// types have been resolved.
//
//golean:export
func (f Function) ValidateFunctionContractMode() Diagnostic {
	if f.Termination != "" && f.Abstract.Size() != 0 {
		return Diagnostic{Code: RecursiveContractRoot, Pos: f.Pos, Detail: ""}
	}
	if f.Abstract.Size() != 0 && f.Laws.Size() == 0 {
		return Diagnostic{Code: UnverifiedContractRoot, Pos: f.Pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidateConcreteTarget checks whether a compiled function may be called
// without a caller-local contract.
//
//golean:export
func (o Object) ValidateConcreteTarget(pos string) Diagnostic {
	if o.Function.UnwrapOr(emptyFunction()).Abstract.Size() != 0 {
		return Diagnostic{Code: CallerLocalContracts, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}
