# Bootstrapping go-lean (ongoing)

go-lean generates Lean models of two packages that it uses to translate Go. The running Go CLI checks its own modeled source, constructs the intermediate representation (IR), and emits Lean definitions. Lean checks laws about parts of that checker and IR construction. The effort is ongoing, with Go source loading and Lean text emission still handled by ordinary Go.

The work began by expressing the compiler IR in modeled Go. Next came the loaded representation and individual subset checks. The current pipeline calls the modeled checker and IR builder directly, replacing the earlier lowering pass with two stages that Lean can model.

## Follow a translation through the core

1. The loader reads Go syntax and type information and records resolved objects, types, expressions, and statements in a `loaded.Program`. The modeled checker works with numeric IDs into those tables. [Source loading](../internal/load) and [loaded representation](../internal/core/loaded/loaded.go)
2. `loaded.Program.Check` checks the subset and builds a checked program. For example, the loader represents a raw loop as a `LoopStmt`, and the statement validator returns a `RawLoop` diagnostic at its source position. [Program checking](../internal/core/loaded/program_check.go) and [validation](../internal/core/loaded/validate.go)
3. `ir.FromLoaded` turns the checked program into IR packages. Expressions, types, and fold operations have explicit variants that the Lean renderer consumes. [IR construction](../internal/core/ir/program.go)
4. The CLI renders the IR as Lean, writes the generated modules, and maintains their Lake roots. The same pipeline handles the core packages when you target them for verification. [CLI generation](../cmd/go-lean/generate.go) and [Lean renderer](../internal/emit)

## Techniques used so far

- **Keep compiler data in the subset.** Generated enums represent syntax and IR variants and support exhaustive case dispatch. Curated arrays hold ID-indexed tables, ordered maps and sets track lookups and membership, and boxes represent recursive data such as checked types and pending frames. [Loaded types](../internal/core/loaded/loaded.go) and [IR types](../internal/core/ir/ir.go)
- **Represent traversal as state transitions.** Body and expression walks keep pending work in explicit frames. Bounded folds drive the checking and construction passes, carrying new state forward and stopping when the work completes or a diagnostic is found. The CLI reports bound exhaustion when a pass returns an incomplete result. [Body traversal](../internal/core/loaded/body.go) and [checker driver](../internal/core/loaded/program_check.go)
- **Prove termination for structural walks.** The IR type walk uses a `sizeOf` measure on checked types. A handwritten Lean module registers the size lemmas for the boxed children so Lean can discharge the decrease obligations. [Type walk](../internal/core/ir/type_walk.go) and [termination lemmas](../internal/core/loaded/checked_type_termination.lean)
- **State laws at the operation they describe.** The loaded package proves lookup and scalar conversion properties, along with subset checks for raw loops, package variables, generic signatures, enum switches, and receiver restrictions. The IR package proves that empty-value construction preserves its type and that selected fold constructors preserve their direct or abstract step target. [Loaded proofs](../internal/core/loaded/loaded_proofs.lean) and [IR proofs](../internal/core/ir/ir_proofs.lean)

## Reproduce the bootstrap check

From the repository root, with Go and Elan on PATH, run:

```sh
go run ./cmd/go-lean verify ./internal/core/...
```

This regenerates the core Lean models and checks both packages through Lake. To follow a single law, start with `rawLoopsRejected` next to `Statement.Validate`. Find its proposition in `loaded.lean`, its proof in `loaded_proofs.lean`, and its checked theorem in `loaded_verify.lean`. The proof checks the full diagnostic, including the position, for every loaded loop statement. [Verification workflow](verification.md#from-go-comment-to-checked-theorem)

## What remains

The current laws establish properties of individual operations on the loaded representation and IR. Broader checker proofs could connect those local checks to accepted programs and establish when the traversal bounds suffice. Laws across the next boundary could show that IR construction preserves the checked program's meaning. An end-to-end semantics-preservation theorem would also need to connect Go source and execution to the loaded representation and the emitted Lean definitions. [Roadmap](roadmap.md)
