package recursive_expr_test

import (
	"testing"

	calc "github.com/frederik-jatzkowski/go-lean/examples/proven/recursive_expr"
)

func TestEvaluate(t *testing.T) {
	expr := calc.Expr_Add(calc.Expr_Constant(1), calc.Expr_Add(calc.Expr_Constant(2), calc.Expr_Constant(3)))
	if got := calc.Eval(expr); got != 6 {
		t.Fatalf("Eval returned %d, want 6", got)
	}
}

func zeroLike[T any](T) T {
	var zero T
	return zero
}

func TestRejectZero(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Error("Eval accepted a zero enum value")
		}
	}()
	calc.Eval(zeroLike(calc.Expr_Constant(1)))
}
