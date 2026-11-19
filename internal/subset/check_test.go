package subset

import (
	"go/token"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

// The numeric encodings must agree with the specification in check_proofs.lean.
func TestBinaryOperatorEncodings(t *testing.T) {
	for _, test := range []struct {
		token                       token.Token
		operator                    ir.Operator
		tokenNumber, operatorNumber int
	}{
		{token.ADD, ir.Add, 12, 0},
		{token.SUB, ir.Subtract, 13, 1},
		{token.MUL, ir.Multiply, 14, 2},
		{token.QUO, ir.Divide, 15, 3},
		{token.REM, ir.Remainder, 16, 4},
		{token.EQL, ir.Equal, 39, 5},
		{token.NEQ, ir.NotEqual, 44, 6},
		{token.LSS, ir.Less, 40, 7},
		{token.LEQ, ir.LessEqual, 45, 8},
		{token.GTR, ir.Greater, 41, 9},
		{token.GEQ, ir.GreaterEqual, 46, 10},
	} {
		if int(test.token) != test.tokenNumber || int(test.operator) != test.operatorNumber {
			t.Errorf("encoding for %v is (%d, %d), want (%d, %d)", test.token, test.token, test.operator, test.tokenNumber, test.operatorNumber)
		}
		if op, ok := Binary(test.token); op != test.operator || !ok {
			t.Errorf("Binary(%v) = (%d, %t), want (%d, true)", test.token, op, ok, test.operator)
		}
	}
	for _, input := range []token.Token{-1, token.ILLEGAL, token.AND} {
		if op, ok := Binary(input); op != 0 || ok {
			t.Errorf("Binary(%v) = (%d, %t), want (0, false)", input, op, ok)
		}
	}
}
