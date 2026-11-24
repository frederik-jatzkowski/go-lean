package emit

import (
	"fmt"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
)

func (r renderer) fold(f ir.Fold) string {
	switch v := f.Case().(type) {
	case ir.CountFold:
		return r.applyFold("count", v.Step, "("+r.expr(v.Count)+").toNat 0", v.Initial)
	case ir.CountUntilFold:
		return r.applyFold("countUntil", v.Step, "("+r.expr(v.Count)+").toNat 0", v.Initial)
	case ir.ListFold:
		return r.applyFold("list", v.Step, r.expr(v.Items), v.Initial)
	case ir.ListUntilFold:
		return r.applyFold("listUntil", v.Step, r.expr(v.Items), v.Initial)
	default:
		panic(fmt.Sprintf("unexpected IR fold %T", v))
	}
}

func (r renderer) applyFold(name string, target ir.FoldStep, input string, initial ir.Expr) string {
	var step string
	switch v := target.Case().(type) {
	case ir.DirectStep:
		step = qualified(v.Target)
	case ir.AbstractStep:
		step = contractVar(v.Target) + ".operation"
	}
	return "(" + r.foldNamespace + "." + name + " " + step + " " + input + " " + r.expr(initial) + ")"
}

func (r renderer) writeFolds(b *strings.Builder, kinds ir.FoldKind) {
	if kinds == 0 {
		return
	}
	b.WriteString("\nnamespace «fold»\n")
	if kinds&ir.FoldN != 0 {
		fmt.Fprintf(b, `
def count {S : Type} (step : %[1]s → S → S) : Nat → %[1]s → S → S
  | 0, _, state => state
  | n + 1, index, state => count step n (index + 1) (step index state)
`, r.word)
	}
	if kinds&ir.FoldNUntil != 0 {
		fmt.Fprintf(b, `
def countUntil {S : Type} (step : %[1]s → S → S × Bool) : Nat → %[1]s → S → S × Bool
  | 0, _, state => (state, false)
  | n + 1, index, state =>
    let next := step index state
    if next.2 then next else countUntil step n (index + 1) next.1
`, r.word)
	}
	if kinds&ir.FoldList != 0 {
		b.WriteString(`
def list {T S : Type} (step : T → S → S) (items : List T) (state : S) : S :=
  items.foldl (fun state item => step item state) state
`)
	}
	if kinds&ir.FoldListUntil != 0 {
		b.WriteString(`
def listUntil {T S : Type} (step : T → S → S × Bool) : List T → S → S × Bool
  | [], state => (state, false)
  | item :: items, state =>
    let next := step item state
    if next.2 then next else listUntil step items next.1
`)
	}
	b.WriteString("\nend «fold»\n")
}
