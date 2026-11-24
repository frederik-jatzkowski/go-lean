package lower

import "github.com/frederik-jatzkowski/go-lean/internal/core/loaded"

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
	default:
		panic("unknown subset diagnostic")
	}
}
