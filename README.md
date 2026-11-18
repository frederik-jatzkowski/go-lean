# Go to Lean

`go-lean` generates Lean 4 definitions for pure Go functions. The examples keep handwritten Lean proofs alongside the generated definitions. Applying those proofs to Go execution currently relies on the correctness of the transpiler.

## Supported

- Ordinary top-level functions with `int64` parameters and one `int64` result. Statically resolved calls can cross package boundaries when the callee's Go body is available and within the supported subset.
- Folded Go constants and runtime `+`, `-`, and `*`. Lean `Int64` models Go's signed 64-bit wraparound. Branches support integer comparisons against values or constants.
- Local bindings and assignments that lower to supported SSA values, plus early returns and branching without control-flow joins. The checker rejects runtime division, loops, recursive or indirect calls, and unsupported effects such as reads of mutable globals.
- Checked proofs for arithmetic identities, wraparound, and clamp bounds and idempotence. The `clampimport` example proves the clamp properties using `Min` and `Max` translated from an imported Go package.

## Select functions to verify

Add `//golean:verify` to a top-level function's doc comment and run `go-lean transpile ./...` from the Go module root. The command scans the packages matched by Go's `./...` pattern, using the active build settings. Each marked source file gets one sibling module, so `clamp.go` generates `clamp_gen.lean`. Each module includes all marked functions in that file and their reachable callees, deduplicated within the module.

The transpiler runs SSA loading, subset and call graph checking, lowering to a structured IR, and Lean generation in that order. Every selected function must pass checking before the command writes any modules. If the last directive is removed from a file, remove its old generated module and update any Lean imports as needed.

## Planned scope

The goal is a deterministic, value-oriented subset of Go whose generated Lean definitions preserve Go's results and modeled panic outcomes. Proofs should carry over to Go execution under the same input assumptions. That requires a semantics-preservation argument for the translation.

### Pure Go

- **Primitive values.** Support `bool`, `string`, signed and unsigned integer types, `rune`, `byte`, `float32`, and `float64`. Preserve fixed-width integer behavior and use the target architecture's width for `int` and `uint`. Model the two float widths with Lean `Float32` and `Float`, accounting for Go's floating-point evaluation semantics.
- **Aggregates and references.** Support structs (including embedded fields), fixed-size arrays, and acyclic pointer structures with controlled aliasing. Support read-only slices and maps, plus local construction and mutation when aliases cannot observe the writes. Map operations must yield deterministic observations.
- **Control flow, generics, and functions.** Expand branching to value and tagless `switch`. Translate bounded `for` loops to recursion with a provably decreasing measure. Map parametric Go type parameters to Lean type parameters. Support pure closures with immutable captures.
- **Purity boundary.** Allow package-level constants. Exclude mutable globals, uncontrolled pointer aliasing and escape, open-ended interface dispatch and type assertions, `unsafe`, reflection, cgo, `init`, `recover`, general-purpose `defer`, I/O, and nondeterministic inputs such as time or randomness. A closed interface set could be modeled as a Lean inductive type. A future restricted form of cleanup would need an explicit model.

### Panics and termination

Model operations such as integer division, indexing, and pointer dereference with `Option` or `Except` outcomes. A panic-freedom theorem then shows that valid inputs always produce a successful outcome. Where a plain value is needed, generate proof obligations for the operation's preconditions, using facts available in the current branch. Loops need a separate termination argument. Fixed-width overflow follows Go's wraparound semantics, with absence of overflow proved as a separate property when required.

### Concurrency

Keep goroutine orchestration outside the initial pure subset. A future extension could translate recognized fan-out/fan-in patterns to a sequential model after establishing race freedom, deterministic results, and equivalence. Channel-based programs would need an explicit process or trace model for scheduling and communication. Deadlock freedom and liveness would be separate properties with stated scheduler assumptions.

## Recommended next step

Add `int64` division with an explicit `Option Int64` result for functions that use it. Use `none` for runtime division by zero and preserve truncation toward zero and the `MinInt64 / -1` wraparound case. Add a guarded-division example with a Lean theorem showing that the guard prevents a division panic, plus regression tests for zero divisors, negative operands, and the signed boundary. This establishes the panic model on the existing scalar types before it is reused for indexing and dereferences.

## Run the examples

Use Go 1.27, Lean 4.36.0, and GNU Make. The [Lean installation guide](https://lean-lang.org/install/manual/) covers Elan, which reads the repository's `lean-toolchain` file. Once Elan is installed, open the repository root in VSCodium with the Lean 4 extension and open an example's `*_proofs.lean` file.

Put theorems in `<example>_proofs.lean` beside the Go source. The proof file imports `<example>_gen.lean`. For example, `clamp_proofs.lean` uses `import clamp.clamp_gen`.

Generated definitions use a namespace based on the Go import path and source filename. Open the relevant namespace in the proof file, such as `GoLean.«github.com/frederik-jatzkowski/go-lean/examples/clamp».clamp`.

From the repository root, run `make generate` after editing the Go examples, then `make check`. The Go tests compare the checked-in definitions with current transpiler output.

| Command | Action |
| --- | --- |
| `make` or `make build` | Build the Go CLI in the repository root |
| `make generate` | Regenerate Lean modules for all marked Go source files |
| `make test` | Run Go tests |
| `make vet` | Run Go vet |
| `make fmt` | Format Go source |
| `make prove` | Check the Lean proofs with Lake |
| `make check` | Run the Go tests, vet, and Lean proofs |
| `make clean` | Remove the CLI binary and Lake build artifacts |

To invoke the transpiler directly from this repository, run:

```sh
go run ./cmd/go-lean transpile ./...
```
