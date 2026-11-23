# Writing and checking laws

## Select a proof target

Start with an observable property of an operation callers use. State the inputs and preconditions, then specify the result, changed state, or rejection that matters. For complex behavior, define the expected rules in an independent Lean module.

Use the exact `//golean:` prefix in the Go doc comment immediately before a function, method, or package clause.

| Directive | Use |
| --- | --- |
| `//golean:verify name : proposition` | Declare a law with a name unique within the Go package. On a function or method, also select the operation for translation. |
| `//golean:verify+ continued proposition` | Continue a law on consecutive comment lines. |
| `//golean:export` | Select a function or concrete method for translation and make it callable from another modeled Go package. |
| `//golean:verify:import Lean.Module` | In a package doc comment, import one dot-separated Lean module into the generated model and law file. |

Package laws can refer to marked operations and their reachable helpers. go-lean collects package directives from all build-selected files. For example, a package doc comment can declare an import and a law together:

```go
//golean:verify:import rules.Reference
//golean:verify resultsAgree : forall n, Step n = Rules.expected n
package example
```

The imported specification must load independently of the model that uses it and its proof and verification companions. Pass modeled operations as arguments to generic specification helpers when needed. The bowling package law passes a roll step to a replay helper and compares the acceptance trace and final score against independent ten-pin rules. [Bowling source](../examples/provable/bowling/bowling.go) and [rules](../examples/provable/bowling/bowling_rules.lean)

## Generate and prove

1. Run `go tool go-lean transpile ./pkg` after editing Go code or directives. Read `<stem>.lean` for the review block, imports, modeled signatures, and formal `Laws` propositions.
2. Write `<stem>_proofs.lean` and import `<stem>.lean`. Declare each theorem in `GoLean.«full/go/import/path».Proofs` with the law's name and generated proposition as its type. Generation preserves an existing proof companion.
3. Run `go tool go-lean verify ./pkg`. The generated `<stem>_verify.lean` imports the model and proof companion, checks theorem types and axiom dependencies, and exposes the `Checked` theorems.

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

Use `go tool go-lean transpile ./...` after moving or deleting Go files, or when a handwritten proof imports a package outside the focused Go dependency graph. Whole-module generation reconciles obsolete generated files and roots in managed source trees. Move handwritten proof companions yourself, updating their imports and namespaces.

## Compose proofs across packages

Each modeled Go package owns a `<stem>.lean` module. It defines selected functions, their reachable helpers, records required by their models, and the package's laws. A modeled record used across packages is declared in the module that owns its Go type.

Add `//golean:export` to a function or method called by another modeled Go package. The generated caller model imports the callee's model. To reuse a checked theorem in a handwritten proof, import the callee's `<stem>_verify` module and refer to `GoLean.«full/go/import/path».Checked.lawName`.

Focused generation includes modeled dependencies. When an emitted dependency declares package laws, generation includes the dependency's marked operations so the laws can refer to them. Managed Lake libraries register generated modules automatically.

### Troubleshoot a failed check

1. **Subset error.** Start at the reported Go location and follow the calls from the marked root. Compare the failing pattern with the supported shapes, then adapt the Go code or state an explicit dependency contract if appropriate. [Supported Go](supported-go.md)
2. **Missing generated import.** Regenerate the whole module, check the imported module name against the path under the Lake library's `srcDir`, and confirm the library configuration covers it.
3. **Missing or mismatched theorem.** Compare the proof name, namespace, and statement with the generated law. Import the merged `<stem>.lean` module. If the axiom check fails, inspect the theorem's dependencies for unfinished proofs or custom axioms.

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
