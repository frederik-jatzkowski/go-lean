// Package recursive_expr evaluates expressions built with private variants.
//
//golean:generate:enum expr { constant, add }
//golean:verify add_evaluates : forall (a b : expr), eval (expr.add a b) = eval a + eval b
package recursive_expr

type constant struct {
	value int64
}

type add struct {
	left, right expr
}

// eval evaluates a constant or a sum.
//
//golean:export
func eval(e expr) int64 {
	return MatchExpr(e, func(c constant) int64 {
		return c.value
	}, func(a add) int64 {
		return eval(a.left) + eval(a.right)
	})
}
