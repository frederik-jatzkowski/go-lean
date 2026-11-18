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
- Generic definitions can use type parameters with the unrestricted `any` constraint as Lean type variables. Calls can use concrete instances of the validated fresh-slice construction, applying a statically known, capture-free, total Go callback to each input element. The checker rejects generic method constraints and other generic call shapes.
- Calls on named interfaces with explicit contracts lower to Lean method projections. The generated function takes a contract containing the method models and their laws.
- Direct calls to local closures can use immutable captured values as extra parameters. Captured cells must be initialized once before use, and closure values stay local to direct calls.
- Named structs with scalar or nested record fields lower to Lean structures. Promoted fields follow the same projection chain as explicit selectors. Field initialization must finish before a local record is read, and the initialization addresses stay local.
- Read-only, nonrecursive record pointer inputs use `Option` to distinguish nil from a record value. Dereferencing nil propagates a panic outcome.
- A nil-guarded, read-only self-recursion on a singly linked input with an `int64` payload lowers to structural recursion on a Lean list. The checker verifies that the step follows the direct next field and uses only pure `int64` arithmetic. The Go input must be a finite, acyclic chain for the proof to apply.
- Read-only slices of supported value elements use Lean lists for indexing by supported Go integer types. Both negative and out-of-range indices propagate a panic at element address formation. Nil and empty slices have the same indexing behavior.
- Read-only maps with integer keys and values use Lean association lists with unique keys. A comma-ok lookup preserves presence separately from the value and gives the Go zero value when a key is absent. Nil and empty maps have the same lookup behavior.
- A function can return a fresh integer map it allocates without a size hint and accesses in straight-line code. The allocation stays local until return. Each write replaces the entry for its key and preserves the other entries. The result uses `Option` to model panic outcomes.
- A function can return a fresh slice matching an input slice's element representation and length, with capacity equal to that length. It initializes each output element once at the current iteration index, using the input element, supported pure arithmetic, or a validated callback in a generic instance. Other functions can return the result of a checked call that constructs a fresh slice. The checker rejects writes to caller-owned storage and escape before return. The result uses `Option` to model panic outcomes.
- Unnamed Go arrays passed by value use fixed-length Lean vectors, with the same checked indexing as slices. Any local SSA array cell must hold an initialized, read-only copy whose address stays local.
- Local bindings, assignments, early returns, branches with boolean conditions, and value and tagless switches. Control-flow joins select the supported scalar value from the branch taken. Short-circuit expressions evaluate their right operand only when needed. The checker rejects unsupported loop and recursion shapes, indirect calls, and effects such as reads of mutable globals.
- A canonical counted loop starts its `uint8` counter at zero, increments it by one while it is below an invariant `uint8` parameter or constant, and returns its sole `int64` accumulator. The accumulator starts from a parameter or constant and updates using pure `int64` arithmetic in a straight-line body. Lean recursion uses the iteration count as decreasing natural-number fuel.
- A range over a read-only `[]int64` parameter updates one `int64` accumulator with straight-line arithmetic and returns it. The checker verifies the generated loop visits each element of the same slice in order, then lowers the update to a Lean left fold over the remaining elements.
- Checked proofs for arithmetic identities, wraparound, clamp bounds and idempotence, and division panic freedom, signed boundaries, and panic propagation. The `clampimport` example proves the clamp properties using `Min` and `Max` translated from an imported Go package.

## Select functions to verify

Add `//golean:verify` to a top-level function's doc comment and run `go-lean transpile ./...` from the Go module root. The command scans the packages matched by Go's `./...` pattern, using the active build settings. Each marked source file gets one sibling module, so `clamp.go` generates `clamp_gen.lean`. Each module includes all marked functions in that file and their reachable callees, deduplicated within the module.

The transpiler runs SSA loading, subset and call graph checking, lowering to a structured IR, and Lean generation in that order. Every selected function must pass checking before the command writes any modules. If the last directive is removed from a file, remove its old generated module and update any Lean imports as needed.

## Interface contracts

Write Lean law fields between `//golean:start` and `//golean:end` in a method's doc comment. For interface-level doc comments use `// golean:start` and `// golean:end` so `gofmt` preserves the block.

```go
type KVStore interface {
    Get(key int64) int64
    //golean:start
    // get_after_put : ∀ s k v, Get (Put s k v) k = v
    //golean:end
    Put(key, value int64) KVStore
}
```

Each generated module includes the contracts it needs for marked functions and their reachable helpers. The generator derives method types from Go, followed by the annotated law fields. Lean checks the fields during `lake build`. Callers take explicit contract arguments, and proofs can use fields such as `contract.get_after_put`.

The contract models valid, non-nil interface handles and total method behavior on those handles. Methods accept supported Go value arguments and return one supported value or a handle of the same interface. Functional updates can return a new handle. Applying a caller proof to Go requires its actual dependency to satisfy the model, including the assumptions about side effects and panics.

The [caller example](examples/provable/kv_store_contract_use/kv_store_contract_use_proofs.lean) proves read-your-writes for any supplied contract. The [implementation example](examples/provable/kv_store_contract_impl/kv_store_contract_impl_proofs.lean) discharges that contract using translated Go functions and specializes the caller theorem. The concrete Go methods delegate to those functions.

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

Run the 15 rejection fixtures individually in the test suite and assert both the rejection reason and its source location.

## Example index

`examples/provable/` contains 36 examples with checked Lean proofs. `make generate` regenerates every module, and `make check` verifies every proof. The examples are `acyclic_list`, `arithmetic`, `array_bounds`, `boolean_implication`, `bounded_counter`, `branch_join`, `byte_rune`, `clamp`, `clampimport`, `constant_conversions`, `division_guarded`, `division_precondition`, `division_propagation`, `embedded_struct`, `float32_rounding`, `float64_special`, `generic_identity`, `generic_map`, `grid_game`, `immutable_closure`, `interface_dispatch`, `kv_store_contract_impl`, `kv_store_contract_use`, `machine_words`, `map_build`, `map_lookup`, `narrow_signed`, `nil_dereference`, `range_fold`, `slice_bounds`, `slice_copy`, `string_bytes`, `struct_fields`, `switch_tagless`, `switch_value`, and `unsigned_wrap`.

### Play the grid game

```sh
go run ./examples/provable/grid_game/cmd/grid-game
go run ./examples/provable/grid_game/cmd/grid-game -wrap
```

Move with W, A, S, or D followed by Enter. Press Q then Enter or send EOF to quit.
The game loop requests each direction through a callback and passes it to the same
Go `Step` function that go-lean translates. In wraparound mode, seam walls keep
the goal room closed across the board edges.

Run `lake build grid_game.grid_game_proofs` to check the [no-win proof](examples/provable/grid_game/grid_game_proofs.lean).
It proves that `Won` returns false after every finite sequence of directions from
`Start`, in either mode. This covers every finite prefix supplied by the callback.

`examples/reject/` contains 15 draft fixtures behind the `golean_reject` build tag. The table records the intended rejection reasons for future tests.

| Fixture | Intended rejection reason |
| --- | --- |
| `global_read` | Reads mutable package state |
| `global_write` | Modifies mutable package state |
| `slice_mutation` | Writes through a caller-owned slice |
| `map_mutation` | Writes through a caller-owned map |
| `escaping_alias` | Returns multiple aliases to caller-owned mutable storage |
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

Compile the draft rejection fixtures with the `golean_reject` build tag.

```sh
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
