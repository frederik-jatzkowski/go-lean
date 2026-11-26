package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// CheckedProgram carries the declarations, dependency order, and checked
// bodies needed to construct IR without inspecting Go syntax.
type CheckedProgram struct {
	Source     Program
	Packages   lean.Array[CheckedPackage]
	NamedTypes lean.OrderedMap[ObjectID, CheckedTypeDeclaration]
}

type CheckedPackage struct {
	Source               Package
	Imports, LeanImports lean.Array[string]
	Declarations         lean.Array[CheckedDeclaration]
	Laws                 lean.Array[CheckedLaw]
	Folds                FoldFlavor
}

type CheckedDeclarationKind uint8

const (
	CheckedNamedType CheckedDeclarationKind = iota + 1
	CheckedMutualTypes
	CheckedAlias
	CheckedNamedConstant
	CheckedFunctionDecl
	CheckedContractDecl
)

type CheckedDeclaration struct {
	Kind     CheckedDeclarationKind
	Object   ObjectID
	Type     CheckedType
	Group    lean.Array[ObjectID]
	Function lean.Option[CheckedFunction]
	Contract lean.Option[CheckedContractDeclaration]
}

type CheckedParameter struct {
	Type    CheckedType
	Binding int
	Name    string
	Unused  bool
}

type CheckedFunction struct {
	Body        lean.Array[CheckedExpr]
	Root        CheckedExprID
	Result      CheckedType
	Params      lean.Array[CheckedParameter]
	Contracts   lean.Array[ObjectID]
	Termination string
}

type CheckedContractDeclaration struct {
	Caller, Callee ObjectID
	Assumptions    lean.Array[Proposition]
	Signature      CheckedContract
}

type CheckedLaw struct {
	Proposition Proposition
	Caller      ObjectID
	Contracts   lean.Array[ObjectID]
}
