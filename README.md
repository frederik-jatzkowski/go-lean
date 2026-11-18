# Go to Lean

`go-lean` generates Lean 4 definitions for pure Go functions. The examples keep handwritten Lean proofs alongside the generated definitions. Applying those proofs to Go execution currently relies on the correctness of the transpiler.

## Supported

- Ordinary top-level functions with integer or `bool` parameters and one result of a supported type. `byte` and `rune` use the same representations as `uint8` and `int32`. Statically resolved calls can cross package boundaries when the callee's Go body is available and within the supported subset.
- Folded Go constants and runtime `+`, `-`, `*`, and `/`. Lean's signed and unsigned fixed-width integer types model Go's wraparound at 8, 16, 32, and 64 bits. Runtime division uses signed truncation toward zero or the unsigned quotient and lifts its function and transitive callers to an `Option` result, with `none` for a zero divisor.
- Go's `int` and `uint` use the target width reported by Go, including for conversions between them. Generated modules expose that width through the `GoTypes.Int` and `GoTypes.UInt` aliases in their source namespace.
- Named integer types use their underlying representation. Go resolves package constants at compile time.
- Go strings model raw bytes with Lean `ByteArray`. Concatenation preserves those bytes, and `len` returns the byte count at the Go target's `int` width.
- `float32` addition uses Lean's binary32 arithmetic. Go constants are emitted as their already-rounded binary32 bits.
- `float64` supports comparisons under IEEE 754, including unordered NaNs and equality of signed zeros. Typed constants preserve their binary64 bits.
- Generic definitions can use type parameters with the unrestricted `any` constraint as Lean type variables. Dynamic interface values, method constraints, and calls to generic functions remain outside the supported subset.
- Direct calls to local closures can use immutable captured values as extra parameters. Captured cells must be initialized once before use, and closure values stay local to direct calls.
- Named structs with scalar or nested record fields lower to Lean structures. Promoted fields follow the same projection chain as explicit selectors. Field initialization must finish before a local record is read, and the initialization addresses stay local.
- Read-only, nonrecursive record pointer inputs use `Option` to distinguish nil from a record value. Dereferencing nil propagates a panic outcome.
- Read-only slices of supported value elements use Lean lists for indexing by supported Go integer types. Both negative and out-of-range indices propagate a panic at element address formation. Nil and empty slices have the same indexing behavior.
- A function can return a fresh slice matching an input slice's element representation and length, with capacity equal to that length. It initializes each output element once at the current iteration index, using the input element and supported pure arithmetic. The checker rejects writes to caller-owned storage and escape before return. The result uses `Option` to model panic outcomes.
- Unnamed Go arrays passed by value use fixed-length Lean vectors, with the same checked indexing as slices. Any local SSA array cell must hold an initialized, read-only copy whose address stays local.
- Local bindings, assignments, early returns, branches with boolean conditions, and value and tagless switches. Control-flow joins select the supported scalar value from the branch taken. Short-circuit expressions evaluate their right operand only when needed. The checker rejects unsupported loops, recursive or indirect calls, and effects such as reads of mutable globals.
- A canonical counted loop starts its `uint8` counter at zero, increments it by one while it is below an invariant `uint8` parameter or constant, and returns its sole `int64` accumulator. The accumulator starts from a parameter or constant and updates using pure `int64` arithmetic in a straight-line body. Lean recursion uses the iteration count as decreasing natural-number fuel.
- A range over a read-only `[]int64` parameter updates one `int64` accumulator with straight-line arithmetic and returns it. The checker verifies the generated loop visits each element of the same slice in order, then lowers the update to a Lean left fold over the remaining elements.
- Checked proofs for arithmetic identities, wraparound, clamp bounds and idempotence, and division panic freedom, signed boundaries, and panic propagation. The `clampimport` example proves the clamp properties using `Min` and `Max` translated from an imported Go package.

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

Apply the panic model to bounds checks and pointer dereferences.

## Example index

`examples/provable/` contains 32 examples. The default build regenerates and checks `arithmetic`, `array_bounds`, `boolean_implication`, `bounded_counter`, `branch_join`, `byte_rune`, `clamp`, `clampimport`, `constant_conversions`, `division_guarded`, `division_precondition`, `division_propagation`, `embedded_struct`, `float32_rounding`, `float64_special`, `generic_identity`, `immutable_closure`, `machine_words`, `narrow_signed`, `nil_dereference`, `range_fold`, `slice_bounds`, `slice_copy`, `string_bytes`, `struct_fields`, `switch_tagless`, `switch_value`, and `unsigned_wrap`. The other 4 have valid Go source behind the `golean_planned` build tag and draft Lean theorem statements with unfinished proofs.

| Area | Pending examples |
| --- | --- |
| Aggregates and references | `map_lookup`, `map_build`, `acyclic_list` |
| Generics and functions | `generic_map` |

`examples/reject/` contains 16 draft fixtures behind the `golean_reject` build tag. The table records the intended rejection reasons for future tests.

| Fixture | Intended rejection reason |
| --- | --- |
| `global_read` | Reads mutable package state |
| `global_write` | Modifies mutable package state |
| `slice_mutation` | Writes through a caller-owned slice |
| `map_mutation` | Writes through a caller-owned map |
| `escaping_alias` | Returns multiple aliases to caller-owned mutable storage |
| `interface_dispatch` | Calls an open-ended interface method |
| `type_assertion` | Inspects the runtime type of an unrestricted interface value |
| `unsafe_pointer` | Exposes a raw memory address |
| `reflection` | Uses runtime reflection |
| `init_function` | Attempts to verify a Go initialization hook |
| `deferred_effect` | Mutates package state on return through `defer` |
| `recover_panic` | Intercepts a panic using `recover` |
| `io_read` | Reads from standard input |
| `nondeterministic_time` | Reads the system clock |
| `unbounded_loop` | Can run indefinitely on odd inputs |
| `goroutine` | Spawns a goroutine and communicates through a channel |

To check that the draft sources compile as Go:

```sh
go test -tags=golean_planned ./examples/provable/...
go test -tags=golean_reject ./examples/reject/...
```

## Run the examples

Use Go 1.27, Lean 4.36.0, and GNU Make. The [Lean installation guide](https://lean-lang.org/install/manual/) covers Elan, which reads the repository's `lean-toolchain` file. Once Elan is installed, open the repository root in VSCodium with the Lean 4 extension and open an example's `*_proofs.lean` file.

Put theorems in `<example>_proofs.lean` beside the Go source. The proof file imports `<example>_gen.lean`. For example, `clamp_proofs.lean` uses `import clamp.clamp_gen`.

Generated definitions use a namespace based on the Go import path and source filename. Open the relevant namespace in the proof file, such as `GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp`.

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
