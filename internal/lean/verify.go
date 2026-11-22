package lean

import (
	"fmt"
	"slices"
	"strconv"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

type Verification struct {
	Module              string
	Scope               ir.Symbol
	ScopedLaws          []gosource.Law
	SeparateLaws        bool
	HasModel            bool
	ModelImports        []string
	LawImports          []string
	Roots               []VerificationRoot
	Constructors        map[ir.Symbol]bool
	PackagePath         string
	ModelModule         string
	DecreaseModule      string
	DecreaseProofModule string
}

type VerificationRoot struct {
	Symbol   ir.Symbol
	Laws     []gosource.Law
	Abstract []AbstractCall
}

type AbstractCall struct {
	Call      ir.Symbol
	Signature ir.Function
	Operation string
	Module    string
	Scope     ir.Symbol
	Laws      []gosource.Law
}

func (r VerificationRoot) canLink() bool {
	for _, target := range r.Abstract {
		if target.Module == "" {
			return false
		}
	}
	return len(r.Abstract) != 0
}

func moduleName(path, suffix string) string {
	parts := strings.Split(path, "/")
	parts[len(parts)-1] += suffix
	for i, part := range parts {
		parts[i] = quoted(part)
	}
	return strings.Join(parts, ".")
}

func PackageModule(path string) string       { return moduleName(path, "_model") }
func DecreaseModule(path string) string      { return moduleName(path, "_decreases") }
func DecreaseProofModule(path string) string { return moduleName(path, "_decreases_proofs") }

func (v Verification) root(symbol ir.Symbol) VerificationRoot {
	for _, root := range v.Roots {
		if root.Symbol == symbol {
			return root
		}
	}
	return VerificationRoot{}
}

const tick = "`"

const declareLaw = `
private def declareGoLaw (name : Lean.Name) (typeText termText source : String) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let parse (text : String) : Lean.Elab.Command.CommandElabM Lean.Term :=
    match Lean.Parser.runParserCategory env ` + tick + `term text source with
    | .ok term => pure ⟨term⟩
    | .error message => throwError "{source}: {message}"
  let type ← parse typeText
  let term ← parse termText
  let ident := Lean.mkIdentFrom (← Lean.getRef) name
  Lean.Elab.Command.elabCommand (← ` + tick + `(def $ident : $type := $term))
`

func emitLaw(out *strings.Builder, name, typ, term string, law gosource.Law) {
	// Use the basename so checked-in output does not depend on the checkout.
	file := strings.ReplaceAll(law.Position.Filename, "\\", "/")
	source := fmt.Sprintf("%s:%d", file[strings.LastIndex(file, "/")+1:], law.Position.Line)
	fmt.Fprintf(out, "\nrun_cmd declareGoLaw `%s %s %s %s\n", name, strconv.Quote(typ), strconv.Quote(term), strconv.Quote(source))
}

func abstractBinder(target AbstractCall) string { return quoted("contract:" + target.Call.Name) }

func abstractType(root VerificationRoot, target AbstractCall) string {
	return "_root_.GoLean." + symbolScope(root.Symbol) + ".AbstractCalls." +
		quoted(root.Symbol.Name) + "." + quoted(target.Call.Name)
}

func (r renderer) renderAbstractContract(out *strings.Builder, root VerificationRoot, target AbstractCall) {
	var signature []string
	for _, param := range target.Signature.Params {
		signature = append(signature, r.leanType(param.Type))
	}
	signature = append(signature, r.leanType(target.Signature.Result))
	operationType := strings.Join(signature, " → ")
	operation := quoted(target.Operation)
	name := strings.TrimPrefix(abstractType(root, target), "_root_.GoLean.")
	for _, law := range target.Laws {
		emitLaw(out, name+".Statements."+quoted(law.Name), "("+operationType+") → Prop",
			"fun "+operation+" => (\n"+law.Proposition+"\n)", law)
	}
	fmt.Fprintf(out, "\nstructure %s where\n  operation : %s\n", name, operationType)
	for _, law := range target.Laws {
		fmt.Fprintf(out, "  %s : %s.Statements.%s operation\n", quoted(law.Name), name, quoted(law.Name))
	}
}

func renderLaws(out *strings.Builder, root VerificationRoot, scope ir.Symbol) {
	fmt.Fprintf(out, "\nnamespace %s\n", symbolScope(scope))
	var quantifiers, arguments []string
	for _, target := range root.Abstract {
		binder := abstractBinder(target)
		quantifiers = append(quantifiers, "("+binder+" : "+abstractType(root, target)+")")
		arguments = append(arguments, binder)
	}
	for _, law := range root.Laws {
		term := law.Proposition
		if len(arguments) != 0 {
			name := quoted(root.Symbol.Name)
			term = "∀ " + strings.Join(quantifiers, " ") + ",\nlet " + name + " := " +
				"_root_.GoLean." + symbolName(root.Symbol) + " " + strings.Join(arguments, " ") + "\n(\n" + term + "\n)"
		}
		emitLaw(out, "Laws."+quoted(law.Name), "Prop", term, law)
	}
	fmt.Fprintf(out, "\nend %s\n", symbolScope(scope))
}

const auditProof = `
private def auditGoProof (companion proof law : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let some owner := env.getModuleIdx? companion | throwError "missing proof module {companion}"
  unless env.getModuleIdxFor? proof == some owner do
    throwError "required proof {proof} must be declared in {companion}"
  let some (.thmInfo info) := env.find? proof | throwError "required proof {proof} must be a theorem"
  let sameType ← Lean.Elab.Command.liftTermElabM (Lean.Meta.isDefEq info.type (Lean.mkConst law))
  unless sameType do
    throwError "required proof {proof} must prove the declared law {law}"
  for axiomName in ← Lean.collectAxioms proof do
    unless [` + tick + `propext, ` + tick + `Quot.sound, ` + tick + `Classical.choice].contains axiomName do
      throwError "required proof {proof} depends on unapproved axiom {axiomName}"
`

func RenderLaws(v Verification) string {
	var out strings.Builder
	out.WriteString(GeneratedHeader + "\nimport Lean.Elab.Command\n")
	model := moduleName(v.Module, "_gen")
	if v.HasModel {
		fmt.Fprintf(&out, "import %s\n", model)
	} else if v.ModelModule != "" {
		model = v.ModelModule
		fmt.Fprintf(&out, "import %s\n", model)
	}
	for _, module := range v.LawImports {
		if module == model && (v.HasModel || v.ModelModule != "") || v.HasModel && slices.Contains(v.ModelImports, module) {
			continue
		}
		fmt.Fprintf(&out, "import %s\n", module)
	}
	out.WriteString(declareLaw)
	out.WriteString("\nnamespace GoLean\n")
	for _, root := range v.Roots {
		renderLaws(&out, root, v.Scope)
	}
	if len(v.ScopedLaws) != 0 {
		renderLaws(&out, VerificationRoot{Laws: v.ScopedLaws}, v.Scope)
	}
	out.WriteString("\nend GoLean\n")
	return out.String()
}

func RenderCheck(v Verification) string {
	var out strings.Builder
	companion := moduleName(v.Module, "_proofs")
	suffix := "_gen"
	if v.SeparateLaws {
		suffix = "_laws"
	}
	fmt.Fprintf(&out, "%s\nimport Lean.Elab.Command\nimport Lean.Util.CollectAxioms\nimport %s\nimport %s\n",
		GeneratedHeader, moduleName(v.Module, suffix), companion)
	imported := make(map[string]bool)
	link := false
	for _, root := range v.Roots {
		if !root.canLink() {
			continue
		}
		link = true
		for _, target := range root.Abstract {
			if target.Module != v.Module && !imported[target.Module] {
				fmt.Fprintf(&out, "import %s\n", moduleName(target.Module, "_verify"))
				imported[target.Module] = true
			}
		}
	}
	out.WriteString(auditProof)
	if link {
		out.WriteString(declareLaw)
	}
	auditRoots := v.Roots
	if len(v.ScopedLaws) != 0 {
		auditRoots = append(slices.Clone(auditRoots), VerificationRoot{Symbol: v.Scope, Laws: v.ScopedLaws})
	}
	for _, root := range auditRoots {
		scope := "GoLean." + symbolScope(v.Scope)
		for _, law := range root.Laws {
			name := quoted(law.Name)
			proof := scope + ".Proofs." + name
			fmt.Fprintf(&out, "\nrun_cmd auditGoProof `%s `%s `%s.Laws.%s\n", companion, proof, scope, name)
			fmt.Fprintf(&out, "theorem %s.Checked.%s : %s.Laws.%s := %s\n", scope, name, scope, name, proof)
		}
	}
	for _, root := range v.Roots {
		if root.canLink() {
			renderLink(&out, root, "GoLean."+symbolScope(v.Scope))
		}
	}
	return out.String()
}

func renderLink(out *strings.Builder, root VerificationRoot, scope string) {
	var arguments []string
	for _, target := range root.Abstract {
		callee := target.Signature.Symbol
		name := scope + ".Linked." + quoted(root.Symbol.Name+"$"+callee.Name)
		arguments = append(arguments, name)
		fmt.Fprintf(out, "\ndef %s : %s where\n  operation := GoLean.%s\n",
			name, abstractType(root, target), symbolName(callee))
		for _, law := range target.Laws {
			fmt.Fprintf(out, "  %s := GoLean.%s.Checked.%s\n", quoted(law.Name), symbolScope(target.Scope), quoted(law.Name))
		}
	}
	concrete := scope + ".Linked." + quoted(root.Symbol.Name)
	args := strings.Join(arguments, " ")
	fmt.Fprintf(out, "\ndef %s := GoLean.%s %s\n", concrete, symbolName(root.Symbol), args)
	fmt.Fprintf(out, "\nnamespace %s.Linked\n", scope)
	for _, law := range root.Laws {
		name := quoted(law.Name)
		emitLaw(out, "Laws."+name, "Prop", law.Proposition, law)
		fmt.Fprintf(out, "theorem %s : Laws.%s := %s.Checked.%s %s\n", name, name, scope, name, args)
	}
	fmt.Fprintf(out, "\nend %s.Linked\n", scope)
}
