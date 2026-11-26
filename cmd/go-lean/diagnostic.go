package main

import (
	"errors"
	"fmt"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
)

func subsetError(issue loaded.Diagnostic) error {
	switch issue.Code {
	case loaded.Valid:
		return nil
	case loaded.UnsupportedBinaryOperator:
		return diagnostic(issue.Pos, "unsupported binary operator %s", issue.Detail)
	case loaded.UnsupportedUnaryOperator:
		return diagnostic(issue.Pos, "unsupported unary operator %s", issue.Detail)
	case loaded.UnsupportedConstantBuiltin:
		return diagnostic(issue.Pos, "unsupported constant builtin call")
	case loaded.UnsupportedExpression:
		return diagnostic(issue.Pos, "unsupported expression %s", issue.Detail)
	case loaded.IfInitializer:
		return diagnostic(issue.Pos, "if initializers are unsupported")
	case loaded.RawLoop:
		return diagnostic(issue.Pos, "raw loops are unsupported in modeled Go; use lean.FoldN, lean.FoldNUntil, lean.FoldList, or lean.FoldListUntil")
	case loaded.InvalidShortDeclaration:
		return diagnostic(issue.Pos, "only immutable short declarations with explicit values are supported")
	case loaded.ExpectedLocalName:
		return diagnostic(issue.Pos, "expected a local name")
	case loaded.InvalidLocalVariableDeclaration:
		return diagnostic(issue.Pos, "expected a single initialized local var declaration")
	case loaded.UnsupportedStatement:
		return diagnostic(issue.Pos, "unsupported statement %s", issue.Detail)
	case loaded.InvalidFunctionSignature:
		return diagnostic(issue.Pos, "expected a concrete, non-variadic function with one result")
	case loaded.InvalidValueReceiver:
		return diagnostic(issue.Pos, "expected a concrete value receiver")
	case loaded.NamedResult:
		return diagnostic(issue.Pos, "named results are unsupported")
	case loaded.InvalidCallTarget:
		return diagnostic(issue.Pos, "expected a direct call to a supported function")
	case loaded.EnumCaseAsCall:
		return diagnostic(issue.Pos, "enum Case() is only supported in an exhaustive enum switch")
	case loaded.InvalidCallReceiver:
		return diagnostic(issue.Pos, "expected a direct call on a concrete value receiver")
	case loaded.InvalidEnumSwitch:
		return diagnostic(issue.Pos, "expected a type switch on enum.Case() without an initializer")
	case loaded.InvalidSwitchClause:
		return diagnostic(issue.Pos, "enum switches require exactly one variant per case and no default")
	case loaded.InvalidReturn:
		return diagnostic(issue.Pos, "expected a return with one value at the end of a block")
	case loaded.DependencyIssue:
		return errors.New(issue.Detail)
	case loaded.ExternalDependency:
		return diagnostic(issue.Pos, "concrete dependency %s must be in the same Go module", issue.Detail)
	case loaded.UnexportedCall:
		return diagnostic(issue.Pos, "cross-package call to %s requires golean:export or a contract", issue.Detail)
	case loaded.UnhandledEnumPayload:
		return diagnostic(issue.Pos, "expected an unhandled enum payload type")
	case loaded.LoadedTypeIssue:
		return errors.New(issue.Detail)
	case loaded.UnsupportedScalarType:
		return diagnostic(issue.Pos, "unsupported scalar type %s", issue.Detail)
	case loaded.UnsupportedGoType:
		return diagnostic(issue.Pos, "unsupported type %s", issue.Detail)
	case loaded.UnsupportedRecordField:
		return diagnostic(issue.Pos, "embedded and blank fields are unsupported")
	case loaded.UnknownLocalOperand:
		return diagnostic(issue.Pos, "expected an immutable local or constant, got %s", issue.Detail)
	case loaded.UnsupportedBinaryOperands:
		return diagnostic(issue.Pos, "unsupported operands for %s", issue.Detail)
	case loaded.PrivateEnumStorage:
		return diagnostic(issue.Pos, "generated enum storage is private to lean.gen.go")
	case loaded.NonEmptyEnumLiteral:
		return diagnostic(issue.Pos, "construct enum values with generated constructors or an empty literal")
	case loaded.UnsupportedCompositeLiteral:
		return diagnostic(issue.Pos, "expected a record literal or an empty curated value")
	case loaded.IncompleteRecordLiteral:
		return diagnostic(issue.Pos, "record literals must initialize every field")
	case loaded.UnkeyedRecordLiteral:
		return diagnostic(issue.Pos, "record literals require keyed fields")
	case loaded.UnsupportedCuratedOperation:
		return diagnostic(issue.Pos, "unsupported curated operation %s", issue.Detail)
	case loaded.InvalidFoldCallback:
		return diagnostic(issue.Pos, "fold step must be a directly named, non-generic function")
	case loaded.MissingFunctionSource:
		return fmt.Errorf("no Go source for %s", issue.Detail)
	case loaded.FunctionSourceIssue:
		return errors.New(issue.Detail)
	case loaded.ActiveFunctionEntry:
		return diagnostic(issue.Pos, "recursive call graph through %s", issue.Detail)
	case loaded.ActiveCallEdge:
		return diagnostic(issue.Pos, "recursive call to %s", issue.Detail)
	case loaded.RecursiveContractRoot:
		return diagnostic(issue.Pos, "measured recursion does not support caller-local contracts")
	case loaded.UnverifiedContractRoot:
		return diagnostic(issue.Pos, "go-lean abstraction requires a verified root")
	case loaded.CallerLocalContracts:
		return diagnostic(issue.Pos, "cannot call a function with caller-local contracts")
	case loaded.MissingContractAssumptions:
		return diagnostic(issue.Pos, "abstract callee %q must name another function with golean:assume laws", issue.Detail)
	case loaded.DuplicateContractTarget:
		return diagnostic(issue.Pos, "duplicate abstract callee %q", issue.Detail)
	case loaded.UnusedContractTarget:
		return diagnostic(issue.Pos, "unused abstract callee %q", issue.Detail)
	case loaded.MissingMeasuredSelfCall:
		return diagnostic(issue.Pos, "termination measure requires a direct recursive call")
	case loaded.InvalidContractSignature:
		return diagnostic(issue.Pos, "abstract callee %s must have a scalar function signature", issue.Detail)
	case loaded.ContractScalarRequired:
		return diagnostic(issue.Pos, "abstract callee %s requires scalar types", issue.Detail)
	case loaded.UnsupportedFunctionDeclaration:
		return diagnostic(issue.Pos, "unsupported function declaration %s", issue.Detail)
	case loaded.UnsupportedGenericAlias:
		return diagnostic(issue.Pos, "unsupported generic type alias %s", issue.Detail)
	case loaded.UnsupportedPackageVariable:
		return diagnostic(issue.Pos, "package variables are unsupported in modeled Go")
	case loaded.UnsupportedDeclaration:
		return diagnostic(issue.Pos, "unsupported package declaration")
	default:
		panic("unknown subset diagnostic")
	}
}

func diagnostic(pos, message string, args ...any) error {
	return fmt.Errorf("%s: %s", pos, fmt.Sprintf(message, args...))
}

func checkError(failure loaded.CheckFailure) error {
	issue := failure.Diagnostic
	switch issue.Code {
	case loaded.TypeCheckBound:
		return diagnostic(issue.Pos, "internal error: enum zero-value traversal exceeded its bound")
	case loaded.EnumZeroCycle:
		names := make([]string, failure.Cycle.Size())
		for index := range names {
			names[index] = failure.Cycle.Get(uint(index)).UnwrapOr("")
		}
		return diagnostic(issue.Pos, "cyclic enum zero value: %s", strings.Join(names, " -> "))
	case loaded.ConstantOutOfRange:
		return diagnostic(issue.Pos, "constant %s is not representable as %s", issue.Detail, failure.Extra)
	case loaded.MissingBodyReturn:
		return diagnostic(issue.Pos, "supported function paths must return a value")
	case loaded.UnreachableBodySuffix:
		return diagnostic(issue.Pos, "unreachable statements after unconditional return")
	case loaded.MissingInitializers:
		return diagnostic(issue.Pos, "local bindings require individual initializers")
	case loaded.ReassignedBinding:
		return diagnostic(issue.Pos, "reassignment is unsupported")
	case loaded.NonExhaustiveMatch:
		return diagnostic(issue.Pos, "non-exhaustive enum switch, missing %s", issue.Detail)
	case loaded.DuplicatePackageLaw:
		return diagnostic(issue.Pos, "duplicate package law %s", issue.Detail)
	case loaded.PackageCheckIssue:
		return errors.New(issue.Detail)
	case loaded.RecursiveEdgeIssue:
		return diagnostic(issue.Pos, "recursive type edge %s -> %s through unsupported container", issue.Detail, failure.Extra)
	case loaded.RecursiveRecordIssue:
		return diagnostic(issue.Pos, "recursive record %s", issue.Detail)
	case loaded.PackageGraphBound:
		return diagnostic(issue.Pos, "internal error: type graph traversal exceeded its bound")
	}
	return subsetError(issue)
}
