# Writing and checking laws

## Select a proof target

Start with an observable property of an operation callers use. State the inputs and preconditions, then specify the result, changed state, rejection, or effects that matter. Keep the expected behavior independent of the implementation. A handwritten rules module can reuse generated types and describe the requirements directly.

Put directives in the declaration's Go doc comment. Use consecutive `//golean:verify+` lines to continue a proposition.

| Directive | Use |
| --- | --- |
| `//golean:verify name : proposition` | Declare a law on a function, concrete method, concrete type, or package. On a function or method, it also selects that operation for translation. Use a unique law name within the Go file. |
| `//golean:export` | Select a function or concrete method for translation so other laws can refer to it. |
| `//golean:verify:import Lean.Module` | In a package comment, make a Lean module available to the package's laws. The imported module can use generated model types. |
| `//golean:assume:import Lean.Module` | In a package comment, import definitions for dependency contracts. These modules load before the model and must be independent of generated models that use them. |

Use a method law for an individual operation, a type law for a property across methods, and a package law for behavior across entry points. Type and package laws can refer to operations selected with `export` or their own `verify` directives.

In the clamp example, the Go comment states the bound as a law on the function:

```go
//golean:verify clampBounds : ∀ value low high : Int64, low ≤ high →
//golean:verify+ low ≤ Clamp value low high ∧ Clamp value low high ≤ high
func Clamp(value, low, high int64) int64 {
	if value < low {
		return low
	}
	if value > high {
		return high
	}
	return value
}
```

In `clamp_proofs.lean`, the theorem imports the generated model and proves the same proposition by following the branches of `Clamp`. The ordered-bounds hypothesis covers the case where the function returns an endpoint.

```lean
import clamp.clamp_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp.Proofs

theorem clampBounds : Laws.clampBounds := by
  intro value low high ordered
  simp only [Clamp, decide_eq_true_eq]
  by_cases below : value < low
  · simpa [below] using ordered
  · by_cases above : high < value
    · simpa [below, above] using ordered
    · simpa [below, above] using And.intro (Int64.not_lt.mp below) (Int64.not_lt.mp above)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp.Proofs
```

The checked-in companion also proves idempotence. [Clamp source](../examples/provable/clamp/clamp.go) and [proof companion](../examples/provable/clamp/clamp_proofs.lean)

## Generate and prove

1. Run `go tool go-lean transpile ./pkg` after editing Go code or directives. Read the signature in `<stem>_gen.lean` before writing the proof. Pay attention to receiver arguments, machine-width integers, result tuples, and any modeled panic outcomes or traces.
2. Write `<stem>_proofs.lean`. Import `<stem>_laws` when it exists, or `<stem>_gen` otherwise. Verification imports and type or package laws produce a separate `_laws` module. Place each theorem under the law's namespace followed by `.Proofs`, using the law's name and its generated proposition as the theorem type.
3. Run `go tool go-lean verify ./pkg` or build the corresponding `<module>.<stem>_verify` target with Lake. The generated verification module checks the named proofs and their axiom dependencies.

### Manage Lake roots

`go tool go-lean setup` creates a managed `lakefile.toml` if the module has no Lake configuration. To opt in with an existing TOML configuration, add these standalone markers to the library's `roots` array:

```toml
[[lean_lib]]
name = "GoLeanProofs"
srcDir = "."
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
```

Set `srcDir` to cover the generated modules and omit `globs`. Include the library in `defaultTargets` to check it with plain `lake build` or whole-module `go tool go-lean verify`. Keep handwritten specs and standalone roots outside the markers, with a trailing comma after each manual entry. When migrating, remove manual entries for modules go-lean will register, including required proof companions. With manual Lake configuration, register the modules yourself.

Use `go tool go-lean transpile ./...` after moving or deleting Go files, or when a proof imports generated modules in other packages. Whole-module generation reconciles obsolete generated files and roots in managed source trees. Move handwritten proof companions yourself, updating their imports and namespaces.

### Troubleshoot a failed check

1. **Subset error.** Start at the reported Go location and follow the calls from the marked root. Compare the failing pattern with the supported shapes, then adapt the Go code or state an explicit dependency contract if appropriate. [Supported Go](supported-go.md)
2. **Missing generated import.** Regenerate the whole module, check the imported module name against the path under the Lake library's `srcDir`, and confirm the library configuration covers it.
3. **Missing or mismatched theorem.** Compare the proof name, namespace, and statement with the generated law. Import `_laws` when present and `_gen` otherwise. If the axiom check fails, inspect the theorem's dependencies for unfinished proofs or custom axioms.

## Work within the supported subset

Small value-based operations with explicit inputs are good starting points. For fixed-size state, see [bowling's value receiver](../examples/provable/bowling/bowling.go). For slice traversal and appending to a fresh result, see the [expression tokenizer](../examples/provable/expression_parser/expression_parser.go). The [map lookup](../examples/provable/map_lookup/map_lookup.go) example covers integer-keyed reads. [Rejection fixtures](../examples/reject) show where generation stops, including global writes, mutation of caller-owned maps, escaping aliases, and goroutines.

Go integer arithmetic wraps at the modeled width. If a property requires mathematical arithmetic, establish the relevant bounds in the law or proof. For potentially panicking operations, inspect the model and prove the guards or preconditions that give a successful result. The [guarded division proof](../examples/provable/division_guarded/division_guarded_proofs.lean) shows that pattern.

## Model a dependency

Use `//golean:assume name : proposition` on a named interface or its methods to state the return-value contract the caller needs. For an interface stored in a value record, `//golean:assume:initialized` models the field as a valid handle, excluding nil and typed-nil values. A value constructor marked `//golean:verify:constructor` can establish initialization from valid inputs when it sets those fields directly from same-type interface parameters on each return path.

Use `//golean:boundary Interface.Method readonly` or `//golean:boundary Interface.Method effect` on a root with a named law. Classify each interface call in its reachable call tree. A read-only call assumes no externally observable effect. An effect call adds the qualified method name to the trace in execution order. The model must be acyclic and total, and every read-only call must occur before any effect on its path. See the [order service walkthrough](order-service.md) for the resulting Lean signature and the assumptions needed to interpret the trace.

## Abstract a concrete call

Add `//golean:abstract Callee` to a caller with a named verification law to model a direct, statically resolved call with the callee's named laws. The name can be a function, `Type.Method`, or an import-qualified form. The callee can supply laws with `//golean:assume name : proposition` or eligible checked `verify` laws. In a concrete assumption, refer to the callee by its unqualified name and pass the receiver first for a method. Consecutive `//golean:assume+` lines continue the proposition.

Signatures must be non-generic and non-variadic, with scalar arguments and a single scalar result. Methods require scalar value receivers. Callers that lower to loop helpers or use recursion fuel are outside this subset. The abstraction applies per caller and callee. A declaration with assumptions alone generates no model on its own.

The caller theorem quantifies over the callee contract. To apply it to Go, establish that the actual callee returns normally, behaves deterministically throughout the modeled execution, has no caller-observable effects beyond the returned value, and meets its laws. When every abstracted callee has eligible checked proofs, the verification module can specialize the caller theorem with those implementations. [Assumed quota](../examples/provable/assumed_quota/assumed_quota.go) and [imported clamp helpers](../examples/provable/clampimport/clampimport.go)
