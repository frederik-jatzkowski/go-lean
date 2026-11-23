# Writing and checking proofs

A law states an observation a caller cares about. Name the inputs and any required preconditions, then describe the result, state transition, or rejection. The [quickstart](quickstart.md) shows the complete cycle for a small function.

Lean checks laws against the generated model. Applying a checked theorem to a Go execution depends on the translation preserving Go semantics, the law's preconditions holding, and runtime dependencies satisfying any declared contracts.

## From Go comment to checked theorem

1. Put a named `//golean:verify` law in a package, function, or method doc comment. The directive selects the whole package. Refer to its modeled operations in the proposition.
2. Run `go tool go-lean transpile ./pkg`. In `<stem>.lean`, read the law review block, generated declarations, and definitions under `Laws`.
3. In `<stem>_proofs.lean`, import the model and declare `theorem lawName : Laws.lawName` in `GoLean.«full/go/import/path».Proofs`. Replace each scaffold `sorry` with a proof. Generation preserves an existing companion.
4. Run `go tool go-lean verify ./pkg`. The generated `<stem>_verify.lean` checks theorem types and axiom dependencies and exposes the proved statements through the package's `Checked` namespace.

## Specify the behavior independently

Use an inline law for a property you can state directly. When several laws share a grammar, execution relation, or substantial rule set, define that vocabulary in a handwritten Lean module and import it with `//golean:verify:import`. The spec must load independently of the model and its companions.

State rules about visible outcomes. For example, bowling gives a strike the next two accepted deliveries as a bonus. The Go scorer maintains pending bonus counters. The proof establishes why those counters implement the rule. Keep that representation invariant in the proof companion. [Bowling walkthrough](../examples/proven/bowling/README.md)

## Use dependencies in a proof

With a concrete call, mark the dependency function with `//golean:export`. The caller model imports the dependency model. Import the dependency's verification module in the handwritten proof to apply its `Checked` theorems. [Imported clamp walkthrough](../examples/proven/clamp_import/README.md)

For an explicit contract on a scalar function, declare its law with `//golean:assume` and name the direct call with `//golean:abstract` on the verified root. The generated function takes contract arguments before its ordinary inputs. Use `dependency0`, `dependency1`, and so on in law propositions, in directive order. A checked caller law is conditional on the runtime dependency returning normally, satisfying the contract, and behaving as the modeled function for the observations the law covers. [Assumed worker walkthrough](../examples/proven/assumed_worker/README.md)

## Register modules with Lake

Setup can create a managed `lakefile.toml`. To opt in with an existing TOML configuration, give the library a local `srcDir` that covers its generated modules, omit `globs`, and add a managed block:

```toml
[[lean_lib]]
name = "GoLeanProofs"
srcDir = "."
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
```

Put handwritten spec roots outside the block. Include the library in `defaultTargets` for a default Lake build. If you manage roots yourself, register the model, proof companion, and verification module. After moving or deleting generated packages, run `go tool go-lean transpile ./...` to reconcile managed roots and files. Move handwritten companions and update their namespaces and imports when their packages move.

## Diagnose a failed check

| Symptom | Where to look |
| --- | --- |
| Unsupported Go | Check the declaration at the reported source location against [Supported Go](supported-go.md). Package checks also cover unused helpers. |
| Missing Lean module | Check the root relative to the library's `srcDir`. Regenerate the workspace if the import is outside the focused Go dependency graph. |
| Missing or mismatched theorem | Compare the generated law, theorem name, and `Proofs` namespace. |
| Axiom check fails | Inspect the theorem's dependencies for unfinished proofs or custom axioms. |
| Termination check fails | Check that the recursive argument decreases the declared measure on each reachable recursive branch. |
