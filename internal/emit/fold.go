package emit

import (
	"fmt"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

var foldNames = map[ir.FoldKind]string{
	ir.FoldN: "count", ir.FoldNUntil: "countUntil",
	ir.FoldList: "list", ir.FoldListUntil: "listUntil",
}

func (r renderer) fold(f ir.Fold) string {
	step := qualified(f.Step)
	if f.Abstract {
		step = contractVar(f.Step) + ".operation"
	}
	input := r.expr(f.Input)
	extra := ""
	if f.Kind == ir.FoldN || f.Kind == ir.FoldNUntil {
		input = "(" + input + ").toNat"
		extra = " 0"
	}
	return "(" + r.foldNamespace + "." + foldNames[f.Kind] + " " + step + " " + input + extra + " " + r.expr(f.Initial) + ")"
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
