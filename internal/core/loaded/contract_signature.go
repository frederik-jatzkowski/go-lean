package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// CheckedContract is the validated scalar signature of a caller-local contract.
type CheckedContract struct {
	Params     lean.List[ScalarKind]
	Result     ScalarKind
	Diagnostic Diagnostic
}

type contractTypes struct {
	Program    Program
	Params     lean.Array[ObjectID]
	Pos, Name  string
	WordBits   int
	Types      lean.List[ScalarKind]
	Diagnostic Diagnostic
}

type contractScalar struct {
	Type       ScalarKind
	Diagnostic Diagnostic
}

func (s contractTypes) scalar(id ObjectID) contractScalar {
	object := s.Program.ObjectOrMissing(id)
	basic := s.Program.Underlying(object.Type)
	if basic.Kind != BasicType {
		issue := Diagnostic{Code: ContractScalarRequired, Pos: s.Pos, Detail: s.Name}
		return contractScalar{Type: NotScalar, Diagnostic: issue}
	}
	kind := basic.Scalar(s.WordBits)
	if kind == NotScalar {
		issue := Diagnostic{Code: UnsupportedScalarType, Pos: s.Pos, Detail: basic.Display}
		return contractScalar{Type: NotScalar, Diagnostic: issue}
	}
	return contractScalar{Type: kind, Diagnostic: validDiagnostic()}
}

func collectContractParam(index uint, state contractTypes) lean.FoldControl[contractTypes] {
	resolved := state.scalar(state.Params.Get(index).UnwrapOr(0))
	next := contractTypes{Program: state.Program, Params: state.Params, Pos: state.Pos, Name: state.Name,
		WordBits: state.WordBits, Types: lean.Cons(resolved.Type, state.Types), Diagnostic: resolved.Diagnostic}
	return lean.FoldControl[contractTypes]{State: next, Stop: resolved.Diagnostic.Code != Valid}
}

func prependContractScalar(kind ScalarKind, kinds lean.List[ScalarKind]) lean.List[ScalarKind] {
	return lean.Cons(kind, kinds)
}

// CheckContractSignature checks a contract's parameters in declaration order
// and its result afterward.
//
//golean:export
func (p Program) CheckContractSignature(object Object, wordBits int, pos string) CheckedContract {
	signature := p.TypeOrMissing(object.Type)
	if signature.Receiver != 0 || signature.Variadic || signature.Generic || signature.Results.Size() != 1 {
		issue := Diagnostic{Code: InvalidContractSignature, Pos: pos, Detail: object.Name}
		return CheckedContract{Params: lean.List[ScalarKind]{}, Result: NotScalar, Diagnostic: issue}
	}
	initial := contractTypes{Program: p, Params: signature.Params, Pos: pos, Name: object.Name,
		WordBits: wordBits, Types: lean.List[ScalarKind]{}, Diagnostic: validDiagnostic()}
	params := lean.FoldNUntil(signature.Params.Size(), initial, collectContractParam)
	if params.Stop {
		return CheckedContract{Params: lean.List[ScalarKind]{}, Result: NotScalar, Diagnostic: params.State.Diagnostic}
	}
	result := initial.scalar(signature.Results.Get(0).UnwrapOr(0))
	ordered := lean.FoldList(params.State.Types, lean.List[ScalarKind]{}, prependContractScalar)
	return CheckedContract{Params: ordered, Result: result.Type, Diagnostic: result.Diagnostic}
}
