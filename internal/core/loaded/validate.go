package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// Diagnostic contains an unformatted subset error. A zero code means success.
type Diagnostic struct {
	Code   DiagnosticCode
	Pos    string
	Detail string
}

type DiagnosticCode uint8

const (
	Valid DiagnosticCode = iota
	UnsupportedBinaryOperator
	UnsupportedUnaryOperator
	UnsupportedConstantBuiltin
	UnsupportedExpression
	IfInitializer
	RawLoop
	InvalidShortDeclaration
	ExpectedLocalName
	InvalidLocalVariableDeclaration
	UnsupportedStatement
	InvalidFunctionSignature
	InvalidValueReceiver
	NamedResult
	InvalidCallTarget
	EnumCaseAsCall
	InvalidCallReceiver
	InvalidEnumSwitch
	InvalidSwitchClause
	InvalidReturn
	DependencyIssue
	ExternalDependency
	UnexportedCall
	UnhandledEnumPayload
	UnsupportedScalarType
	LoadedTypeIssue
	UnsupportedGoType
	UnsupportedRecordField
	UnknownLocalOperand
	UnsupportedBinaryOperands
	PrivateEnumStorage
	NonEmptyEnumLiteral
	UnsupportedCompositeLiteral
	IncompleteRecordLiteral
	UnkeyedRecordLiteral
	UnsupportedCuratedOperation
	InvalidFoldCallback
	MissingFunctionSource
	ActiveFunctionEntry
	FunctionSourceIssue
	ActiveCallEdge
	RecursiveContractRoot
	UnverifiedContractRoot
	CallerLocalContracts
	MissingContractAssumptions
	DuplicateContractTarget
	UnusedContractTarget
	MissingMeasuredSelfCall
	InvalidContractSignature
	ContractScalarRequired
	UnsupportedFunctionDeclaration
	UnsupportedGenericAlias
	UnsupportedPackageVariable
	UnsupportedDeclaration
	TypeCheckBound
	EnumZeroCycle
	ConstantOutOfRange
	MissingBodyReturn
	UnreachableBodySuffix
	MissingInitializers
	ReassignedBinding
	NonExhaustiveMatch
	DuplicatePackageLaw
	PackageCheckIssue
	RecursiveEdgeIssue
	RecursiveRecordIssue
	PackageGraphBound
)

func validDiagnostic() Diagnostic {
	return Diagnostic{Code: Valid, Pos: "", Detail: ""}
}

// ValidateDependency checks a concrete dependency after resolving its package.
//
//golean:export
func (p Package) ValidateDependency(target Package, path string, pos string) Diagnostic {
	if p.Path == path {
		return validDiagnostic()
	}
	if target.Issue != "" {
		return Diagnostic{Code: DependencyIssue, Pos: "", Detail: target.Issue}
	}
	if p.Module == "" || target.Module != p.Module {
		return Diagnostic{Code: ExternalDependency, Pos: pos, Detail: path}
	}
	return validDiagnostic()
}

// ValidateConcreteCall checks visibility independently of call-graph state.
//
//golean:export
func (o Object) ValidateConcreteCall(caller string, pos string) Diagnostic {
	if o.Package == caller {
		return validDiagnostic()
	}
	if o.Function.IsSome() {
		if o.Function.UnwrapOr(emptyFunction()).Export {
			return validDiagnostic()
		}
	}
	return Diagnostic{Code: UnexportedCall, Pos: pos, Detail: o.FullName}
}

func (e Expression) binaryDiagnostic(form BinaryExpr) Diagnostic {
	op := form.Operator
	if op == "+" || op == "-" || op == "==" || op == "!=" ||
		op == "<" || op == "<=" || op == ">" || op == ">=" ||
		op == "&&" || op == "||" {
		return validDiagnostic()
	}
	return Diagnostic{Code: UnsupportedBinaryOperator, Pos: e.Pos, Detail: op}
}

// Validate checks the expression's own form. Its children and referenced
// objects are checked when they are visited in the enclosing program.
//
//golean:export
func (e Expression) Validate() Diagnostic {
	switch form := e.Form.Case().(type) {
	case UnsupportedExpr:
		return e.unsupportedExpression()
	case Parenthesized:
		return validDiagnostic()
	case Identifier:
		return validDiagnostic()
	case UnaryExpr:
		if e.Constant.Present {
			if form.Operator == "-" || form.Operator == "+" || form.Operator == "!" {
				return validDiagnostic()
			}
			return Diagnostic{Code: UnsupportedUnaryOperator, Pos: e.Pos, Detail: form.Operator}
		}
		if form.Operator == "!" {
			return validDiagnostic()
		}
		return e.unsupportedExpression()
	case BinaryExpr:
		return e.binaryDiagnostic(form)
	case SelectorExpr:
		if form.Selection.Kind == FieldValue && form.Selection.Direct {
			return validDiagnostic()
		}
		return e.unsupportedExpression()
	case CompositeExpr:
		return validDiagnostic()
	case KeyedExpr:
		return e.unsupportedExpression()
	case CallExpr:
		if e.Constant.Present && !form.Conversion {
			return Diagnostic{Code: UnsupportedConstantBuiltin, Pos: e.Pos, Detail: ""}
		}
		return validDiagnostic()
	}
	return validDiagnostic()
}

func (e Expression) unsupportedExpression() Diagnostic {
	if e.Constant.Present {
		return validDiagnostic()
	}
	return Diagnostic{Code: UnsupportedExpression, Pos: e.Pos, Detail: e.Syntax}
}

type shortDeclarationCheck struct {
	Names      lean.Array[Binding]
	Diagnostic Diagnostic
}

func checkLocalName(index uint, state shortDeclarationCheck) lean.FoldControl[shortDeclarationCheck] {
	binding := state.Names.Get(index).UnwrapOr(Binding{Pos: "", Object: 0, Identifier: false})
	if !binding.Identifier {
		problem := Diagnostic{Code: ExpectedLocalName, Pos: binding.Pos, Detail: ""}
		return lean.FoldControl[shortDeclarationCheck]{State: shortDeclarationCheck{Names: state.Names, Diagnostic: problem}, Stop: true}
	}
	return lean.FoldControl[shortDeclarationCheck]{State: state, Stop: false}
}

// Validate checks the statement's own form. Checks that depend on the enclosing
// block or the types and identities of referenced objects belong to traversal.
//
//golean:export
func (s Statement) Validate() Diagnostic {
	switch form := s.Form.Case().(type) {
	case UnsupportedStmt:
		return Diagnostic{Code: UnsupportedStatement, Pos: s.Pos, Detail: form.Syntax}
	case ReturnStmt:
		return validDiagnostic()
	case IfStmt:
		if form.HasInitializer {
			return Diagnostic{Code: IfInitializer, Pos: s.Pos, Detail: ""}
		}
		return validDiagnostic()
	case SwitchStmt:
		return validDiagnostic()
	case LoopStmt:
		return Diagnostic{Code: RawLoop, Pos: s.Pos, Detail: ""}
	case ShortDecl:
		if !form.ValidForm {
			return Diagnostic{Code: InvalidShortDeclaration, Pos: s.Pos, Detail: ""}
		}
		initial := shortDeclarationCheck{Names: form.Names, Diagnostic: validDiagnostic()}
		checked := lean.FoldNUntil(form.Names.Size(), initial, checkLocalName)
		return checked.State.Diagnostic
	case VarDecl:
		if !form.ValidForm {
			return Diagnostic{Code: InvalidLocalVariableDeclaration, Pos: s.Pos, Detail: ""}
		}
		return validDiagnostic()
	}
	return validDiagnostic()
}

// ValidateSignature checks a function's signature before lowering its types.
//
//golean:export
func (f Function) ValidateSignature(signature Type, result Object) Diagnostic {
	if signature.Variadic || signature.Generic || signature.Results.Size() != 1 || !f.HasBody {
		return Diagnostic{Code: InvalidFunctionSignature, Pos: f.Pos, Detail: ""}
	}
	if signature.Receiver != 0 && !signature.ValueReceiver {
		return Diagnostic{Code: InvalidValueReceiver, Pos: f.Pos, Detail: ""}
	}
	if result.Name != "" {
		return Diagnostic{Code: NamedResult, Pos: f.Pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidateTarget checks the resolved object of a nonconstant call.
//
//golean:export
func (c CallExpr) ValidateTarget(target Object, pos string) Diagnostic {
	if target.Kind != FunctionObject || target.Package == "" || c.Ellipsis {
		return Diagnostic{Code: InvalidCallTarget, Pos: pos, Detail: ""}
	}
	if target.EnumCase != 0 {
		return Diagnostic{Code: EnumCaseAsCall, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidateReceiver checks ordinary Go method dispatch.
//
//golean:export
func (c CallExpr) ValidateReceiver(signature Type, pos string) Diagnostic {
	if c.Selection.Kind != NoSelection && (!signature.ValueReceiver || !c.Selection.Direct) {
		return Diagnostic{Code: InvalidCallReceiver, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidateCaseMethod checks that the resolved switch receiver uses an enum's
// generated case method.
//
//golean:export
func (s SwitchStmt) ValidateCaseMethod(method Object, pos string) Diagnostic {
	if s.CaseMethod == 0 || method.EnumCase == 0 {
		return Diagnostic{Code: InvalidEnumSwitch, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}

// Validate checks the case clause's shape before visiting its body.
//
//golean:export
func (c SwitchClause) Validate() Diagnostic {
	if c.Count != 1 {
		return Diagnostic{Code: InvalidSwitchClause, Pos: c.Pos, Detail: ""}
	}
	return validDiagnostic()
}

// ValidatePosition checks the return's result count and placement in the block.
//
//golean:export
func (r ReturnStmt) ValidatePosition(pos string, last bool) Diagnostic {
	if r.Values.Size() != 1 || !last {
		return Diagnostic{Code: InvalidReturn, Pos: pos, Detail: ""}
	}
	return validDiagnostic()
}
