package lean

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

// RenderDecreases declares measures and call-site propositions without the
// recursive definitions. A handwritten proof companion can import this module.
func RenderDecreases(program ir.Program, verification Verification) string {
	var out strings.Builder
	r := renderer{wordBits: program.WordBits, records: program.Records, contracts: program.Contracts}
	out.WriteString(GeneratedHeader + "\nimport Lean.Elab.Term\n")
	for _, module := range verification.ModelImports {
		fmt.Fprintf(&out, "import %s\n", module)
	}
	out.WriteString(declareMeasure + "\nset_option linter.unusedVariables false\n\nnamespace GoLean\n")
	r.renderModelTypes(&out, verification.PackagePath, verification.PackagePath)
	r.renderDecreaseDeclarations(&out, program.Functions)
	out.WriteString("\nend GoLean\n")
	return out.String()
}

func (r renderer) renderDecreaseDeclarations(out *strings.Builder, functions []ir.Function) {
	for _, fn := range functions {
		if fn.Decreases == "" {
			continue
		}
		recur := recursiveRenderer{renderer: r, fn: fn}
		fmt.Fprintf(out, "\nnamespace %s\n", symbolNamespace(fn.Symbol))
		fmt.Fprintf(out, "\ndef %s", recur.measureName())
		r.renderParams(out, fn.Params)
		fmt.Fprintln(out, " : Nat :=")
		for _, param := range fn.Params {
			if param.Name != "_" {
				fmt.Fprintf(out, "  let %s := %s\n", quoted(param.Name), binderName(param))
			}
		}
		fmt.Fprintf(out, "  go_measure%% %s\n", strconv.Quote(fn.Decreases))
		recur.pathObligations(out, fn.Body, nil, "")
		fmt.Fprintf(out, "\nend %s\n", symbolNamespace(fn.Symbol))
	}
}

const declareMeasure = `
local elab "go_measure% " source:str : term => do
  let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) ` + tick + `term source.getString with
    | .ok parsed => pure parsed
    | .error message => throwError "{message}"
  Lean.Elab.Term.elabTerm parsed (some (Lean.mkConst ` + tick + `Nat))
`

type recursiveRenderer struct {
	renderer
	fn   ir.Function
	site int
}

type decreaseContext struct {
	binder, typ string
	value       string // An empty value introduces a universally quantified local.
}

func (r recursiveRenderer) measureName() string { return quoted(r.fn.Symbol.Name + "$measure") }

func (r recursiveRenderer) obligationName(site int) string {
	return r.fn.Symbol.Name + "$decrease" + strconv.Itoa(site)
}

func (r recursiveRenderer) args() []string {
	args := make([]string, 0, len(r.fn.Params))
	for _, param := range r.fn.Params {
		args = append(args, binderName(param))
	}
	return args
}

func (r recursiveRenderer) comparison(call ir.Call) string {
	args := make([]string, 0, len(call.Args))
	for _, arg := range call.Args {
		args = append(args, r.renderExpr(arg))
	}
	return fmt.Sprintf("%s %s < %s %s", r.measureName(), strings.Join(args, " "), r.measureName(), strings.Join(r.args(), " "))
}

func (r recursiveRenderer) local(binding ir.Binding) decreaseContext {
	local := decreaseContext{binder: binderName(binding.Binder), typ: r.leanType(binding.Binder.Type)}
	// Successful monadic binds and earlier calls supply values independent of
	// this recursive definition. Quantifying over them is conservative.
	if _, call := binding.Value.(ir.Call); !binding.CanPanic && !call {
		local.value = r.renderExpr(binding.Value)
	}
	return local
}

func (r recursiveRenderer) guard(condition ir.Expr, path string, branch bool) decreaseContext {
	return decreaseContext{binder: "guard" + path, typ: fmt.Sprintf("(%s) = %t", r.renderExpr(condition), branch)}
}

func (r *recursiveRenderer) pathObligations(out *strings.Builder, body ir.Body, context []decreaseContext, path string) {
	for _, binding := range body.Bindings {
		if call, ok := binding.Value.(ir.Call); ok && call.RecursiveSite != "" {
			r.site++
			fmt.Fprintf(out, "\n-- Recursive Go call at %s\ndef %s : Prop :=\n  ∀", call.RecursiveSite, quoted(r.obligationName(r.site)))
			r.renderParams(out, r.fn.Params)
			fmt.Fprintln(out, ",")
			for _, local := range context {
				if local.value == "" {
					fmt.Fprintf(out, "  ∀ (%s : %s),\n", local.binder, local.typ)
				} else {
					fmt.Fprintf(out, "  let %s : %s := %s\n", local.binder, local.typ, local.value)
				}
			}
			fmt.Fprintf(out, "  %s\n", r.comparison(call))
		}
		context = append(context, r.local(binding))
	}
	if branch, ok := body.Result.(ir.If); ok {
		r.pathObligations(out, branch.Then, append(context, r.guard(branch.Condition, path+"T", true)), path+"T")
		r.pathObligations(out, branch.Else, append(context, r.guard(branch.Condition, path+"F", false)), path+"F")
	}
}

const auditRecursion = `
private def auditGoDecrease (declaration : Lean.Name) (source : String) :
    Lean.Elab.Command.CommandElabM Unit := do
  for axiomName in ← Lean.collectAxioms declaration do
    unless [` + tick + `propext, ` + tick + `Quot.sound, ` + tick + `Classical.choice].contains axiomName do
      throwError "{source}: {declaration} depends on unapproved axiom {axiomName}"
`

func (r renderer) renderRecursiveFunction(out *strings.Builder, fn ir.Function, companion bool) {
	recur := recursiveRenderer{renderer: r, fn: fn}
	fmt.Fprintf(out, "\nnamespace %s\n", symbolNamespace(fn.Symbol))
	recur.pathProofs(out, fn.Body, companion)
	fmt.Fprintf(out, "\ndef %s", quoted(fn.Symbol.Name))
	r.renderParams(out, fn.Params)
	fmt.Fprintf(out, " : Option %s := do\n", r.leanType(fn.Result))
	recur.site = 0
	recur.body(out, fn.Body, "  ", nil, "")
	fmt.Fprintf(out, "termination_by %s %s\ndecreasing_by all_goals first | assumption | (simp_wf; assumption)\n", recur.measureName(), strings.Join(recur.args(), " "))
	fmt.Fprintf(out, "\nrun_cmd auditGoDecrease %s%s %s\n", tick+tick, quoted(fn.Symbol.Name), strconv.Quote("recursive "+fn.Symbol.Name))
	fmt.Fprintf(out, "\nend %s\n", symbolNamespace(fn.Symbol))
}

func (r *recursiveRenderer) pathProofs(out *strings.Builder, body ir.Body, companion bool) {
	for _, binding := range body.Bindings {
		call, ok := binding.Value.(ir.Call)
		if !ok || call.RecursiveSite == "" {
			continue
		}
		r.site++
		name := r.obligationName(r.site)
		fmt.Fprintf(out, "\nset_option linter.unusedSimpArgs false in\nprivate theorem %s : %s := by\n  first\n",
			quoted(name+"$proof"), quoted(name))
		if companion {
			fmt.Fprintf(out, "  | exact Decreases.%s\n", quoted(name))
		}
		fmt.Fprintf(out, "  | unfold %s\n    intros\n    first\n", quoted(name))
		fmt.Fprintln(out, "    | assumption")
		fmt.Fprintf(out, "    | simp_all (config := { zetaDelta := true }) [%s,\n", r.measureName())
		var rules []string
		for _, bits := range []int{8, 16, 32, 64} {
			rules = append(rules, fmt.Sprintf("        UInt%d.lt_iff_toNat_lt, UInt%d.le_iff_toNat_le, ← UInt%d.toNat_inj, UInt%d.toNat_sub",
				bits, bits, bits, bits))
		}
		fmt.Fprintf(out, "%s] <;> omega\n", strings.Join(rules, ",\n"))
		fmt.Fprintf(out, "    | simp (config := { zetaDelta := true }) only [%s]\n      fail %s\n", r.measureName(), strconv.Quote("could not prove "+name+" for the Go call at "+call.RecursiveSite+
			"; supply theorem Decreases."+name+" in the package decreases proof companion"))
		fmt.Fprintf(out, "\nrun_cmd auditGoDecrease %s%s %s\n", tick+tick, quoted(name+"$proof"), strconv.Quote(call.RecursiveSite))
	}
	if branch, ok := body.Result.(ir.If); ok {
		r.pathProofs(out, branch.Then, companion)
		r.pathProofs(out, branch.Else, companion)
	}
}

func (r *recursiveRenderer) body(out *strings.Builder, body ir.Body, indent string, context []decreaseContext, path string) {
	for _, binding := range body.Bindings {
		if call, ok := binding.Value.(ir.Call); ok && call.RecursiveSite != "" {
			r.site++
			args := r.args()
			for _, local := range context {
				if local.value == "" {
					args = append(args, local.binder)
				}
			}
			fmt.Fprintf(out, "%shave decrease%d : %s := %s %s\n", indent, r.site, r.comparison(call), quoted(r.obligationName(r.site)+"$proof"), strings.Join(args, " "))
			fmt.Fprintf(out, "%slet %s : %s ← %s\n", indent, binderName(binding.Binder), r.leanType(binding.Binder.Type), r.renderExpr(call))
		} else {
			r.renderBindings(out, []ir.Binding{binding}, indent)
		}
		context = append(context, r.local(binding))
	}
	switch result := body.Result.(type) {
	case ir.If:
		then := r.guard(result.Condition, path+"T", true)
		fmt.Fprintf(out, "%sif %s : %s then\n", indent, then.binder, r.renderExpr(result.Condition))
		r.body(out, result.Then, indent+"  ", append(context, then), path+"T")
		fmt.Fprintf(out, "%selse\n", indent)
		// Lean represents a false Bool guard as the negation of its coercion.
		// Give the independent obligation the explicit Boolean equality.
		alias := r.guard(result.Condition, path+"F", false)
		fmt.Fprintf(out, "%s  have %s : %s := Bool.eq_false_iff.mpr %s\n", indent, alias.binder, alias.typ, then.binder)
		r.body(out, result.Else, indent+"  ", append(context, alias), path+"F")
	default:
		r.renderBody(out, ir.Body{Result: result}, indent, true)
	}
}
