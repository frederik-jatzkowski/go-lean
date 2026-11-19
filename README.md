# Go to Lean

`go-lean` generates Lean 4 definitions for pure Go functions. The examples keep handwritten Lean proofs alongside the generated definitions. Applying those proofs to Go execution currently relies on the correctness of the transpiler.

## Set up and verify a Go module

Install Go and Lean, then run these commands from the Go module root with `go-lean` on PATH.

```sh
go-lean setup
go-lean doctor
go-lean verify
```

`setup` creates missing Lean workspace files and installs the go-lean skill at `.agents/skills/go-lean/SKILL.md`. It preserves existing files. `doctor` checks workspace files and whether `go`, `lake`, and `lean` are on PATH. Use `go-lean doctor --fix` to create missing workspace files before checking again.

`verify` regenerates Lean modules and runs the workspace's default Lake build, forwarding its output and exit status. Use `go-lean verify ./pkg` for a single Go package or `go-lean verify ./pkg/...` to include its subpackages. Lake also builds any Lean modules imported by the selected targets. If those imports refer to generated modules outside the selection, generate them first with `go-lean transpile ./...`.

Use `go-lean transpile <path>` to generate without running Lake. Both commands accept `.` for the root package and `./...` for the whole module. Use whole-module generation to clean up managed modules after deleting a Go file.

## Supported

- Ordinary top-level functions with integer or `bool` parameters and one or more supported results. `byte` and `rune` use the same representations as `uint8` and `int32`. Statically resolved calls can cross package boundaries when the callee's Go body is available and within the supported subset.
- Declared, non-generic concrete methods with one or more supported results can be marked or called directly. The receiver uses the existing value representation or the read-only record pointer model. A nil receiver can return normally if the method does not dereference it. Bound method values and synthetic method wrappers are unsupported. The bounded stateful subset below handles receiver writes.
- Folded Go constants and runtime `+`, `-`, `*`, `/`, and `%`. Lean's signed and unsigned fixed-width integer types model Go's wraparound at 8, 16, 32, and 64 bits. Runtime division uses signed truncation toward zero or the unsigned quotient. A nonzero signed remainder has the sign of the dividend, including when the divisor is negative. Taking the remainder of the minimum signed value with divisor `-1` gives zero. Runtime division and remainder lift the function and transitive callers to an `Option` result, with `none` for a zero divisor.
- Go's `int` and `uint` use the target width reported by Go, including for conversions between them. Generated modules expose that width through the `GoTypes.Int` and `GoTypes.UInt` aliases in their source namespace.
- Named integer types use their underlying representation. Go resolves package constants at compile time.
- Go strings model raw bytes with Lean `ByteArray`. Concatenation preserves those bytes, and `len` returns the byte count at the Go target's `int` width.
- `float32` addition uses Lean's binary32 arithmetic. Go constants are emitted as their already-rounded binary32 bits.
- `float64` supports IEEE 754 comparisons. Go's `==` lowers to Lean's Boolean `==`. Lean's propositional `=` expresses logical equality. NaNs are unordered, so Go's `x != x` tests whether `x` is NaN. Positive and negative zero compare equal. Typed constants preserve their binary64 bits. See the [floating-point comparison example](examples/provable/float64_special/float64_special.go).
- Generic definitions can use type parameters with the unrestricted `any` constraint as Lean type variables. Calls can use concrete instances whose bodies pass the checker. The generic fresh-slice construction can apply a statically known callback with immutable captures and propagates a callback panic in traversal order. The checker rejects generic method constraints.
- Calls on named interfaces with explicit contracts lower to Lean method projections. The generated function takes a contract containing the method models and their laws.
- Direct calls to local closures can use immutable captured values as extra parameters. Captured cells must be initialized once before use, and closure values stay local to direct calls.
- Named structs with supported scalar, nested record, array, or read-only slice fields lower to Lean structures. Promoted fields follow the same projection chain as explicit selectors. Local record fields start at Go zero values and can be assigned, including nested fields and branch-dependent updates, while their addresses stay local.
- Read-only, nonrecursive record pointer inputs use `Option` to distinguish nil from a record value. Dereferencing nil propagates a panic outcome.
- A nil-guarded, read-only self-recursion on a singly linked input with an integer payload lowers to structural recursion on a Lean list. The step follows the direct next field, uses supported integer arithmetic, and passes additional parameters unchanged. The Go input must be a finite, acyclic chain for the proof to apply.
- Read-only slices of supported value elements use Lean lists for indexing by supported Go integer types and for `len`. Both negative and out-of-range indices propagate a panic at element address formation. Nil and empty slices have the same indexing behavior.
- A slice field can be initialized, replaced as a whole, tested against nil, measured with `len`, and read by index. Its Lean model uses `Option (List …)` to distinguish nil from non-nil empty slices. Ordinary functions generated in the same module also preserve that distinction for slice parameters and results when the module uses slice fields or compares slices with nil. Indexed writes to slice fields are unsupported.
- Read-only maps with integer keys and values support `m[k]` and comma-ok lookup. They use Lean association lists with unique keys. An absent key gives the Go zero value, and comma-ok lookup also reports whether the key is present. Nil and empty maps have the same lookup behavior. Go leaves map iteration order unspecified. The subset checker rejects all map `range` loops, including order-independent folds. It also rejects `len(m)`.
- A function can return a fresh integer map it allocates with or without a size hint and accesses through acyclic control flow. A map literal with multiple entries requires constant keys. The allocation stays local until return. Each write replaces the entry for its key and preserves the other entries. The result uses `Option` to model panic outcomes.
- A function can return a fresh slice with the input length and capacity equal to that length. It can use `copy` for matching elements or initialize each output element once at the current range or counted index. Checked transforms can change the element type, branch, call supported helpers, or invoke a validated callback in a generic instance. Other functions can return the result of a checked call that constructs a fresh slice. The checker rejects writes to caller-owned storage and escape before return. The result uses `Option` to model panic outcomes.
- Unnamed Go arrays passed by value or stored in record fields use fixed-length Lean vectors. Indexed writes are supported on local arrays and array fields, including value-receiver copies, while element addresses stay local. Unchecked indices propagate bounds panics. Constant in-range indices and recognized unsigned guards such as `if i < len(a)` can yield total accesses. The Nine Men’s Morris board uses this model.
- Local bindings, assignments, early returns, branches with boolean conditions, and value and tagless switches. Control-flow joins select the supported scalar value from the branch taken. Short-circuit expressions evaluate their right operand only when needed. The checker rejects unsupported loop and recursion shapes, indirect calls, and effects such as reads of mutable globals.
- A counted loop increments an integer counter by one while it is below an invariant bound of the same type. It can compute its start, bound, and accumulator seed before the loop, update scalar loop-carried values in a straight-line or conditional body, and compute a result after the loop. Lean recursion uses the nonnegative distance from start to bound as fuel.
- A range or zero-based indexed traversal over a read-only slice can update scalar accumulators, including conditional updates and multiple values carried across iterations. The checker verifies that the traversal visits each element of the same slice in order and lowers it to a Lean left fold.
- Checked proofs for arithmetic identities, wraparound, clamp bounds and idempotence, and division panic freedom, signed boundaries, and panic propagation. The `clampimport` example proves the clamp properties using `Min` and `Max` translated from an imported Go package.

## Select functions to verify

Add a named `//golean:verify` law to a function or concrete method’s doc comment. Use `//golean:export` to generate a model without declaring a law. Run `go-lean transpile ./...` from the Go module root. The command scans the packages matched by Go's `./...` pattern, using the active build settings. Each marked source file gets a sibling model module, so `clamp.go` generates `clamp_gen.lean`. The model includes the marked functions and methods and their reachable concrete callees, deduplicated within the module.

The transpiler runs SSA loading, subset and call graph checking, lowering to a structured IR, and Lean generation in that order. Every selected function must pass checking before the command writes any modules. If the last directive is removed from a file, remove its old generated module and update any Lean imports as needed.

### Laws declared in Go

Declare each law in the doc comment that matches its scope. Use a function or method comment for an operation, a concrete type comment for behavior across its methods, and the package comment for behavior across package entry points. Each law has a name unique to the Go file and a Lean proposition. Use consecutive `//golean:verify+` lines to continue it. For type or package laws, select the operations with `//golean:export` or their own verification directives.

```go
//golean:verify clampBounds : ∀ value low high : Int64, low ≤ high →
//golean:verify+ low ≤ Clamp value low high ∧ Clamp value low high ≤ high
```

Write each proof in `<stem>_proofs.lean` under the source file's Lean namespace followed by `.Proofs`. A theorem named `clampBounds` can use `Laws.clampBounds` as its statement. The proof companion imports `<stem>_laws` when generated and `<stem>_gen` otherwise. Building `<stem>_verify` checks that the companion supplies each theorem, its type matches the Go law, and its dependencies use only the allowed Lean axioms. Run `go tool task generate` after Go edits and `go tool task check` to check generated-file freshness and build the proofs.

### Managed Lake roots

Add the two markers to a library's `roots` array in `lakefile.toml` once. Set `srcDir` to cover the generated modules and omit `globs` so Lake builds the listed roots. Include the library in `defaultTargets` to check its proofs with plain `lake build`.

```toml
[[lean_lib]]
name = "Proofs"
srcDir = "."
roots = [
  # BEGIN go-lean managed roots
  # END go-lean managed roots
]
```

Run `go-lean transpile ./...` from the project root to register generated modules and the proof companions required by active verification modules. When migrating, remove their existing manual entries from the array. Reserve the marker text for standalone lines inside managed `roots` arrays. Keep handwritten reference modules and standalone Lean roots outside the markers, with a trailing comma on each manual entry. Projects without markers continue to register modules manually.

When directives change or Go files move, transpile removes obsolete generated roots and prunes obsolete files with the go-lean generated header in managed source trees. It keeps generated files for Go sources excluded by the current build configuration. Move any handwritten proof companions yourself and update their imports and namespaces before building.

### Import Lean modules into Go laws

Put import directives in package doc comments. Their scope is the Go package.

| Directive | When the module is loaded |
| --- | --- |
| `//golean:verify:import Lean.Module` | When Lean elaborates verification laws, after the generated model. A reference spec can import `*_gen` to use its state types. |
| `//golean:assume:import Lean.Module` | When Lean elaborates the model and its contracts. The import also reaches downstream callers that model these contracts. Verification laws can use the imported definitions too. |

An assumption import must load before the model whose contracts use it. Keep it independent of that model to avoid an import cycle. This also applies to a verified operation law reused as an abstract callee contract.

Verification imports and type or package laws cause generation of a separate `<stem>_laws.lean`. For a package law in a dedicated `doc.go`, import the generated operation models explicitly with `//golean:verify:import` and use qualified Lean names. A law-only file generates `doc_laws.lean` and `doc_verify.lean`.

[Bowling](examples/provable/bowling/README.md) demonstrates all three placements. [Nine Men's Morris](examples/provable/nine_mens_morris/README.md) imports a reference spec that shares the generated game and board types.

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

### Interface call allowlists and effect traces

A function or method with a named verification law can list interface calls using `//golean:boundary Interface.Method readonly` or `//golean:boundary Interface.Method effect`. Use `pkg.Interface.Method` for imported declarations. Once a root has a classified entry, every interface call in its checked call tree must be listed, including calls inside direct helpers. Each entry must be used. Callbacks, legacy callee abstractions, and opaque calls are outside this subset.

The Go signature is unchanged. The strict root's Lean result is a pair of the usual return value and a `List String`. Each `effect` invocation contributes an entry named `import/path.Interface.Method` in execution order, including repeated invocations. A `readonly` invocation contributes no entry and assumes that the implementation has no externally observable effects. Existing interface contracts supply the return values in both cases and must describe those values throughout the sequence. The checker requires an acyclic, total model and rejects any path where a `readonly` invocation follows an effect, including across helper calls.

Use the trace to prove when a call occurs. In the [fraud withdrawal example](examples/provable/fraud_withdrawal/fraud_withdrawal.go), Lean proves an empty trace on rejection and one setter call on approval. The Go adapter tests cover persistence, and the empty-trace guarantee depends on the adapters honoring their read-only classifications.

## Multiple results

Go results become right-nested Lean products in declaration order. For example,
`(int64, bool, uint8)` becomes `Int64 × (Bool × UInt8)`. A call that can panic
returns one `Option` around the whole product, even when the caller discards
some or all results. Stateful methods put the product in the result component
of the receiver transition. Interface contracts and callbacks retain their
single-result signatures.

The [self-proof](internal/subset/check_proofs.lean) checks the generated model of
`subset.Binary` for all operator tokens. Use `go tool task generate` to regenerate its
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

The contract models valid, non-nil interface handles and total method behavior on those handles. Methods accept supported Go value arguments and can return one supported value or a handle of the same interface. A method with no Go result returns Lean `Unit` in the contract. Strict effect traces record classified void calls just like calls with a result. Functional updates can return a new handle. Applying a caller proof to Go requires its actual dependency to satisfy the model, including the assumptions about side effects and panics. The [order service example](examples/provable/order_service/README.md) uses a void persistence port.

The [lowering interfaces](internal/lower/contract.go) use this mechanism to describe checked SSA input and persistent lowering state.

### Initialized interface fields

Place `//golean:assume:initialized` in the field doc comment to use a named interface field in a verified value method or function. A named Go struct can mix supported ordinary fields with multiple annotated interface fields. The Lean record stores one handle per field, and calls through those fields use the existing interface contracts, including through statically resolved helpers.

The directive is a precondition of the method proof. In Go, each annotated field must hold a valid dependency, excluding nil interfaces and typed-nil values, and the dependency must satisfy its interface contract. The Go zero value of the struct remains available to callers. Verified code can read annotated fields from values and pass them to checked callees. Pointer access and mutation of these fields are outside this subset.

Optionally mark a function with `//golean:verify:constructor`. It generates a checked `<Function>$initialized` theorem for the returned struct. The theorem models interface parameters as optional handles and proves that every annotated field is present when the input dependencies are present. Each return path must construct a struct that assigns its annotated fields directly from same-type interface parameters. Constructor verification adds no runtime behavior and is independent of method verification. The initial subset covers value-returning constructors with direct injection. Runtime nil validation and constructors with failure results are outside this subset.

The [fraud withdrawal example](examples/provable/fraud_withdrawal/fraud_withdrawal.go) proves that a blocked withdrawal returns the original balance and is rejected. It also proves the behavior for invalid amounts and approved withdrawals.

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

`examples/provable/` contains 41 examples with checked Lean proofs. `go tool task generate` regenerates every module, and `go tool task check` verifies every proof. The examples are `acyclic_list`, `arithmetic`, `array_bounds`, `batch_fulfillment`, `boolean_implication`, `bounded_counter`, `branch_join`, `byte_rune`, `clamp`, `clampimport`, `constant_conversions`, `division_guarded`, `division_precondition`, `division_propagation`, `embedded_struct`, `float32_rounding`, `float64_special`, `generic_identity`, `generic_map`, `grid_game`, `immutable_closure`, `integer_remainder`, `interface_dispatch`, `kv_store_contract_impl`, `kv_store_contract_use`, `machine_words`, `map_build`, `map_lookup`, `movement_arrival`, `multi_result`, `narrow_signed`, `nil_dereference`, `range_fold`, `slice_bounds`, `slice_copy`, `string_bytes`, `struct_fields`, `switch_tagless`, `switch_value`, `territory_methods`, and `unsigned_wrap`.

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

### Play Nine Men's Morris

```sh
go run ./examples/provable/nine_mens_morris/cmd/morris
lake build nine_mens_morris.morris_verify
```

Two players share the terminal and enter the numbered points shown on the
board. Enter one point to place or capture, two points to move, or `q` to quit.
The [example guide](examples/provable/nine_mens_morris/README.md) explains the
rule variant and the scope of its Lean proofs.

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

Use Go 1.27 and Lean 4.36.0. The Go module pins Task, which you can run with `go tool task`. The [Lean installation guide](https://lean-lang.org/install/manual/) covers Elan, which reads the repository's `lean-toolchain` file. Once Elan is installed, open the repository root in VSCodium with the Lean 4 extension and open an example's `*_proofs.lean` file.

Put theorems in `<example>_proofs.lean` beside the Go source. The proof file imports the generated law module when present. For example, bowling uses `import bowling.bowling_laws`, and clamp uses `import clamp.clamp_gen`.

Generated definitions use a namespace based on the Go import path and source filename. A concrete method uses the name `«Receiver$Method»` and takes its receiver as the first Go value parameter. Open the relevant namespace in the proof file, such as `GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp`.

From the repository root, run `go tool task generate` after editing the Go examples, then `go tool task check`. The Go tests compare the checked-in definitions with current transpiler output.

| Command | Action |
| --- | --- |
| `go tool task` or `go tool task build` | Build the Go CLI in the repository root |
| `go tool task generate` | Regenerate Lean modules for all marked Go source files |
| `go tool task test` | Run Go tests |
| `go tool task vet` | Run Go vet |
| `go tool task fmt` | Format Go source |
| `go tool task prove` | Check the Lean proofs with Lake |
| `go tool task check` | Run the Go tests, vet, and Lean proofs |
| `go tool task clean` | Remove the CLI binary and Lake build artifacts |

To invoke the transpiler directly from this repository, run:

```sh
go run ./cmd/go-lean transpile ./...
```
