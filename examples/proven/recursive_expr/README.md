# Recursive expressions

The calculator defines two private variants. Its public constructors let an ordinary Go caller build a tree using type inference.

```go
one := calc.Expr_Constant(1)
two := calc.Expr_Constant(2)
three := calc.Expr_Constant(3)
value := calc.Eval(calc.Expr_Add(one, calc.Expr_Add(two, three))) // 6
```

`Eval` uses an exhaustive `MatchExpr` and recurses on the two children of an addition. The Lean law checks that evaluating an addition yields the sum of its children's values using `Int64` arithmetic.

```sh
go test ./examples/proven/recursive_expr
go run ./cmd/go-lean verify ./examples/proven/recursive_expr
```
