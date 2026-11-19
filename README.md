# Go to Lean

`go-lean` generates Lean 4 definitions for pure Go functions. The examples keep handwritten Lean proofs alongside the generated definitions. Applying those proofs to Go execution currently relies on the correctness of the transpiler.

## Supported

- Ordinary top-level functions with integer or `bool` parameters and one or more supported results. `byte` and `rune` use the same representations as `uint8` and `int32`. Statically resolved calls can cross package boundaries when the callee's Go body is available and within the supported subset.
- Declared, non-generic concrete methods with one or more supported results can be marked or called directly. The receiver uses the existing value representation or the read-only record pointer model. A nil receiver can return normally if the method does not dereference it. Bound method values and synthetic method wrappers are unsupported. The bounded stateful subset below handles receiver writes.
- Folded Go constants and runtime `+`, `-`, `*`, `/`, and `%`. Lean's signed and unsigned fixed-width integer types model Go's wraparound at 8, 16, 32, and 64 bits. Runtime division uses signed truncation toward zero or the unsigned quotient. A nonzero signed remainder has the sign of the dividend, including when the divisor is negative. Taking the remainder of the minimum signed value with divisor `-1` gives zero. Runtime division and remainder lift the function and transitive callers to an `Option` result, with `none` for a zero divisor.
- Go's `int` and `uint` use the target width reported by Go, including for conversions between them. Generated modules expose that width through the `GoTypes.Int` and `GoTypes.UInt` aliases in their source namespace.
- Named integer types use their underlying representation. Go resolves package constants at compile time.
- Go strings model raw bytes with Lean `ByteArray`. Concatenation preserves those bytes, and `len` returns the byte count at the Go target's `int` width.
- `float32` addition uses Lean's binary32 arithmetic. Go constants are emitted as their already-rounded binary32 bits.
- `float64` supports comparisons under IEEE 754, including unordered NaNs and equality of signed zeros. Typed constants preserve their binary64 bits.
- Generic definitions can use type parameters with the unrestricted `any` constraint as Lean type variables. Calls can use concrete instances whose bodies pass the checker. The generic fresh-slice construction can apply a statically known callback with immutable captures and propagates a callback panic in traversal order. The checker rejects generic method constraints.
- Calls on named interfaces with explicit contracts lower to Lean method projections. The generated function takes a contract containing the method models and their laws.
- Direct calls to local closures can use immutable captured values as extra parameters. Captured cells must be initialized once before use, and closure values stay local to direct calls.
- Named structs with scalar or nested record fields lower to Lean structures. Promoted fields follow the same projection chain as explicit selectors. Local record fields start at Go zero values and can be assigned, including nested fields and branch-dependent updates, while their addresses stay local.
- Read-only, nonrecursive record pointer inputs use `Option` to distinguish nil from a record value. Dereferencing nil propagates a panic outcome.
- A nil-guarded, read-only self-recursion on a singly linked input with an integer payload lowers to structural recursion on a Lean list. The step follows the direct next field, uses supported integer arithmetic, and passes additional parameters unchanged. The Go input must be a finite, acyclic chain for the proof to apply.
- Read-only slices of supported value elements use Lean lists for indexing by supported Go integer types and for `len`. Both negative and out-of-range indices propagate a panic at element address formation. Nil and empty slices have the same indexing behavior.
- Read-only maps with integer keys and values use Lean association lists with unique keys. An absent key gives the Go zero value. A comma-ok lookup also returns presence separately. Nil and empty maps have the same lookup behavior.
- A function can return a fresh integer map it allocates with or without a size hint and accesses through acyclic control flow. A map literal with multiple entries requires constant keys. The allocation stays local until return. Each write replaces the entry for its key and preserves the other entries. The result uses `Option` to model panic outcomes.
- A function can return a fresh slice with the input length and capacity equal to that length. It can use `copy` for matching elements or initialize each output element once at the current range or counted index. Checked transforms can change the element type, branch, call supported helpers, or invoke a validated callback in a generic instance. Other functions can return the result of a checked call that constructs a fresh slice. The checker rejects writes to caller-owned storage and escape before return. The result uses `Option` to model panic outcomes.
- Unnamed Go arrays passed by value use fixed-length Lean vectors, with the same checked indexing as slices. Any local SSA array cell must hold an initialized, read-only copy whose address stays local.
- Local bindings, assignments, early returns, branches with boolean conditions, and value and tagless switches. Control-flow joins select the supported scalar value from the branch taken. Short-circuit expressions evaluate their right operand only when needed. The checker rejects unsupported loop and recursion shapes, indirect calls, and effects such as reads of mutable globals.
- A counted loop increments an integer counter by one while it is below an invariant bound of the same type. It can compute its start, bound, and accumulator seed before the loop, update scalar loop-carried values in a straight-line or conditional body, and compute a result after the loop. Lean recursion uses the nonnegative distance from start to bound as fuel.
- A range or zero-based indexed traversal over a read-only slice can update scalar accumulators, including conditional updates and multiple values carried across iterations. The checker verifies that the traversal visits each element of the same slice in order and lowers it to a Lean left fold.
- Checked proofs for arithmetic identities, wraparound, clamp bounds and idempotence, and division panic freedom, signed boundaries, and panic propagation. The `clampimport` example proves the clamp properties using `Min` and `Max` translated from an imported Go package.

## Select functions to verify

Add a named `//golean:verify` law to a function or concrete method’s doc comment. Use `//golean:export` to generate a model without declaring a law. Run `go-lean transpile ./...` from the Go module root. The command scans the packages matched by Go's `./...` pattern, using the active build settings. Each marked source file gets a sibling model module, so `clamp.go` generates `clamp_gen.lean`. The model includes the marked functions and methods and their reachable concrete callees, deduplicated within the module.

The transpiler runs SSA loading, subset and call graph checking, lowering to a structured IR, and Lean generation in that order. Every selected function must pass checking before the command writes any modules. If the last directive is removed from a file, remove its old generated module and update any Lean imports as needed.

### Laws declared in Go

The examples and lowering self-proofs declare their laws in Go doc comments. Each law has a name unique to the Go file and a Lean proposition. Use consecutive `//golean:verify+` lines to continue it.

```go
//golean:verify clampBounds : ∀ value low high : Int64, low ≤ high →
//golean:verify+ low ≤ Clamp value low high ∧ Clamp value low high ≤ high
```

Write each proof in `<stem>_proofs.lean` under the generated model's namespace followed by `.Proofs`. A theorem named `clampBounds` can use `Laws.clampBounds` as its statement. Add the model, proof, and generated `<stem>_verify.lean` modules to the default Lake library's roots. Lake checks that the companion supplies each theorem, its type matches the Go law, and its dependencies use only the allowed Lean axioms. Run `make generate` after Go edits and `make check` to check generated-file freshness and build the proofs.

### Abstract calls and assumed laws

Use `//golean:assume <name> : <Lean proposition>` on a function or concrete method to specify a boundary for a caller. Continue a proposition with consecutive `//golean:assume+` lines. Each law name is unique within the declaration. Use the unqualified Go function or method name for the Lean operation and pass a method's receiver as its first argument.

```go
//golean:assume quotaBound : ReadQuota ≤ 10
func ReadQuota() int64 { return configuredQuota }

//golean:abstract ReadQuota
//golean:verify deniesEleven : CanSpend 11 = false
func CanSpend(cost int64) bool { return cost <= ReadQuota() }
```

A caller with a named verification law can abstract a direct, statically resolved call using `Function`, `Type.Method`, `pkg.Function`, or `pkg.Type.Method`. The caller and callee must have non-generic, non-variadic scalar signatures with one scalar result. Methods require a scalar value receiver. Callers that lower to loop helpers or use recursion fuel are unsupported.

The caller opts in per callee. An ordinary call or a separately selected verification root still goes through subset checking. An assumption-only declaration generates no Lean module of its own. The caller's Lean model takes a contract containing the operation and its law proofs, and the checked theorem quantifies over that contract. Applying the theorem to the Go implementation requires evidence that the callee returns without panicking, behaves as a single deterministic operation throughout the modeled execution, has no effects observable by the caller beyond its return value, and satisfies the laws.

Examples cover a [global configuration read](examples/provable/assumed_quota/assumed_quota.go), a [goroutine-backed helper](examples/provable/assumed_worker/assumed_worker.go), and a [reflection-backed method](examples/provable/assumed_reflection/assumed_reflection.go). When every abstract callee supplies checked `verify` laws, the verification module also specializes the theorem with the concrete operations and their proofs, as in [ClampImport](examples/provable/clampimport/clampimport.go).

## Multiple results

Go results become right-nested Lean products in declaration order. For example,
`(int64, bool, uint8)` becomes `Int64 × (Bool × UInt8)`. A call that can panic
returns one `Option` around the whole product, even when the caller discards
some or all results. Stateful methods put the product in the result component
of the receiver transition. Interface contracts and callbacks retain their
single-result signatures.

The [self-proof](internal/subset/check_proofs.lean) checks the generated model of
`subset.Binary` for all operator tokens. Use `make generate` to regenerate its
Lean definition and `lake build SelfProofs` to check the proof.

## Bounded stateful methods

A concrete pointer-receiver method can use named `//golean:verify` laws or `//golean:export`. A method that writes its receiver, directly or through a checked same-receiver helper, can use a single tracked record, supported value fields, and read-only value slices. The checker accepts direct field assignment and checked helper calls, including void helpers. It rejects escaping addresses, writes through other pointers, and writes to slice elements. Slice operations include `len`, checked indexing, nil assignment, and direct calls to the standard library's `slices.Clone`. Lean represents these slices as optional lists so nil and empty remain distinguishable.

The bounded loop shape uses an `int` receiver field as the cursor and another receiver field as the slice. The loop can follow straight-line receiver setup, tests `cursor < len(slice)`, and increments the cursor once on each path back to the test. Helpers on continuing paths must preserve the cursor and slice. Branches and early exits can update the state, including replacing the slice on an exit path. The loop guard's signed distance supplies structural recursion fuel. Use Go-representable slice lengths when applying the proofs.

The result is `Option (Option Receiver × Result)`, where an inner `none` is a nil receiver and an outer `none` is a modeled panic. A void helper uses `Unit` for its result. Panic outcomes omit intermediate writes and callback history.

A stateful method can take one directly invoked, non-nil unary Boolean callback with a supported scalar argument. Lean supplies its answer as a function of the zero-based call index and the actual argument. The result becomes `Option (Option Receiver × Result × List Argument)`, with the callback arguments in call order. Applying a proof assumes the callback terminates normally and leaves the receiver and all slice storage read by the invocation untouched. Concurrent writes to that state are outside the model. Other callback effects can influence later answers and remain outside the theorem.

The [movement example](examples/provable/movement_arrival/movement_arrival_proofs.lean) checks the first future or blocked step and the order of entry queries. The [batch fulfillment example](examples/provable/batch_fulfillment/batch_fulfillment_proofs.lean) proves that a successful return preserves the order list, keeps initially nonnegative stock nonnegative, and accounts for the stock debit over the processed prefix.

## Interface contracts

Write each Lean law field on its own `//golean:assume <name> : <proposition>` line in the interface or method doc comment. Repeat the directive for each law. These lines survive `gofmt`.

```go
type KVStore interface {
    Get(key int64) int64
    //golean:assume get_after_put : ∀ s k v, Get (Put s k v) k = v
    Put(key, value int64) KVStore
}
```

Each generated module includes the contracts it needs for marked functions and their reachable helpers. The generator derives method types from Go, followed by the annotated law fields. Lean checks the fields during `lake build`. Callers take explicit contract arguments, and proofs can use fields such as `contract.get_after_put`.

The contract models valid, non-nil interface handles and total method behavior on those handles. Methods accept supported Go value arguments and return one supported value or a handle of the same interface. Functional updates can return a new handle. Applying a caller proof to Go requires its actual dependency to satisfy the model, including the assumptions about side effects and panics.

The [lowering interfaces](internal/lower/contract.go) use this mechanism to describe checked SSA input and persistent lowering state.

The [caller example](examples/provable/kv_store_contract_use/kv_store_contract_use_proofs.lean) proves read-your-writes for any supplied contract. The [implementation example](examples/provable/kv_store_contract_impl/kv_store_contract_impl_proofs.lean) discharges that contract using translated Go functions and specializes the caller theorem. The concrete Go methods delegate to those functions.

## Planned scope

The goal is a deterministic, value-oriented subset of Go whose generated Lean definitions preserve Go's results and modeled panic outcomes. Proofs should carry over to Go execution under the same input assumptions. That requires a semantics-preservation argument for the translation.

### Pure Go

- **Primitive values.** Support `bool`, `string`, signed and unsigned integer types, `rune`, `byte`, `float32`, and `float64`. Preserve fixed-width integer behavior and use the target architecture's width for `int` and `uint`. Model the two float widths with Lean `Float32` and `Float`, accounting for Go's floating-point evaluation semantics.
- **Aggregates and references.** Support structs (including embedded fields), fixed-size arrays, and acyclic pointer structures with controlled aliasing. Support read-only slices and maps, plus local construction and mutation when aliases cannot observe the writes. Map operations must yield deterministic observations.
- **Control flow, generics, and functions.** Expand branching to value and tagless `switch`. Translate bounded `for` loops to recursion with a provably decreasing measure. Map parametric Go type parameters to Lean type parameters. Support pure closures with immutable captures.
- **Purity boundary.** Allow package-level constants. Exclude mutable globals, uncontrolled pointer aliasing and escape, open-ended interface dispatch and type assertions, `unsafe`, reflection, cgo, `init`, `recover`, general-purpose `defer`, I/O, and nondeterministic inputs such as time or randomness. A closed interface set could be modeled as a Lean inductive type. A future restricted form of cleanup would need an explicit model.

### Panics and termination

Model operations such as integer division and remainder, indexing, and pointer dereference with `Option` or `Except` outcomes. A panic-freedom theorem then shows that valid inputs always produce a successful outcome. Where a plain value is needed, generate proof obligations for the operation's preconditions, using facts available in the current branch. Loops need a separate termination argument. Fixed-width overflow follows Go's wraparound semantics, with absence of overflow proved as a separate property when required.

### Concurrency

Keep goroutine orchestration outside the initial pure subset. A future extension could translate recognized fan-out/fan-in patterns to a sequential model after establishing race freedom, deterministic results, and equivalence. Channel-based programs would need an explicit process or trace model for scheduling and communication. Deadlock freedom and liveness would be separate properties with stated scheduler assumptions.

## Recommended next step

Run the 15 rejection fixtures individually in the test suite and assert both the rejection reason and its source location.

## Example index

`examples/provable/` contains 41 examples with checked Lean proofs. `make generate` regenerates every module, and `make check` verifies every proof. The examples are `acyclic_list`, `arithmetic`, `array_bounds`, `batch_fulfillment`, `boolean_implication`, `bounded_counter`, `branch_join`, `byte_rune`, `clamp`, `clampimport`, `constant_conversions`, `division_guarded`, `division_precondition`, `division_propagation`, `embedded_struct`, `float32_rounding`, `float64_special`, `generic_identity`, `generic_map`, `grid_game`, `immutable_closure`, `integer_remainder`, `interface_dispatch`, `kv_store_contract_impl`, `kv_store_contract_use`, `machine_words`, `map_build`, `map_lookup`, `movement_arrival`, `multi_result`, `narrow_signed`, `nil_dereference`, `range_fold`, `slice_bounds`, `slice_copy`, `string_bytes`, `struct_fields`, `switch_tagless`, `switch_value`, `territory_methods`, and `unsigned_wrap`.

The [territory methods example](examples/provable/territory_methods/territory_methods_proofs.lean) proves that a territory at its configured cap cannot claim another tile and that dereferencing a nil territory produces a panic outcome.

The [integer remainder example](examples/provable/integer_remainder/integer_remainder_proofs.lean) proves calendar day bounds and rollover, signed remainder behavior, and a zero-period fallback.

### Play the grid game

```sh
go run ./examples/provable/grid_game/cmd/grid-game
go run ./examples/provable/grid_game/cmd/grid-game -wrap
```

Move with W, A, S, or D followed by Enter. Press Q then Enter or send EOF to quit.
The game loop requests each direction through a callback and passes it to the same
Go `Step` function that go-lean translates. In wraparound mode, seam walls keep
the goal room closed across the board edges.

Run `lake build grid_game.grid_game_verify` to check the [no-win proof](examples/provable/grid_game/grid_game_proofs.lean) against its Go declaration.
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

Generated definitions use a namespace based on the Go import path and source filename. A concrete method uses the name `«Receiver$Method»` and takes its receiver as the first Go value parameter. Open the relevant namespace in the proof file, such as `GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp`.

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
