---
name: go-lean
description: Write, refactor, and verify idiomatic Go with go-lean. Use when choosing proof targets, declaring Go laws, checking Lean proofs, or modeling dependency contracts and effect traces.
---

# Getting started

go-lean's main purpose is to prove observable behavior at Go package boundaries. It translates marked Go functions and methods and their reachable supported helpers into Lean definitions. Lean checks the laws you state about those definitions. Applying a theorem to Go execution relies on the correctness of the translation, the stated input preconditions, and the behavior of any modeled dependencies.

- Use the Go version in [go.mod](../../../go.mod) and the Lean version in [lean-toolchain](../../../lean-toolchain). Install Elan using the [Lean installation guide](https://lean-lang.org/install/manual/) and confirm `lake --version` from the project root. The repository pins Go Task as a Go tool.
- In this repository, run `go tool task generate` followed by `go tool task check`. The direct equivalents are `go run ./cmd/go-lean transpile ./...` for generation and `go test ./...`, `go vet ./...`, and `lake build` for checks.
- For another Go module, build the CLI here with `go tool task build`, then invoke that binary by absolute path as `go-lean transpile ./...` from the consuming module root. Use the `.exe` binary on Windows. Put `lean-toolchain` and `lakefile.toml` at that root and configure a Lean library whose source directory covers the generated files. Add a [managed Lake roots block](../../../README.md#managed-lake-roots) to opt into automatic registration and cleanup.

Follow [clamp.go](../../../examples/provable/clamp/clamp.go) for a complete example. Its `clampBounds` law states that ordered bounds contain the result. Generation defines `Laws.clampBounds` in `clamp_gen.lean`. The [proof companion](../../../examples/provable/clamp/clamp_proofs.lean) imports `clamp.clamp_gen` and proves `theorem clampBounds : Laws.clampBounds` in the model namespace's `.Proofs` namespace. Run `lake build clamp.clamp_verify` from the repo root to check the companion against the law.

# Best Proof Practices

- Specify the behavior callers should observe in Lean and prove that the generated Go model satisfies it. State the preconditions and quantify over the relevant inputs. Include rejection, the full returned state, and observable effects when they are part of the contract.
- Keep the specification independent of the implementation. Reuse generated data types when they fit, and define expected behavior directly from the requirements. Avoid calling translated implementation helpers to compute the expected result. During review, ask whether the specification would reject a plausible implementation bug, then check the specification itself against the intended behavior.
- Match the specification to the claim. A few direct laws can describe a small function such as clamp. For a state machine, define the initial state, legal actions, transitions, and outcomes in a handwritten Lean module. Prove agreement for each action and use induction to extend it to action histories from the initial state.
- Use Lean's Boolean `==` in laws about Go `float64` equality. For example, a law that Go considers two values equal can assert `(x == y) = true`. This uses propositional equality to state the result of the Boolean comparison. See [supported floating-point comparisons](../../../README.md#supported).
- Follow the [Morris rules](../../../examples/provable/nine_mens_morris/morris_rules.lean) and [proofs](../../../examples/provable/nine_mens_morris/morris_proofs.lean) for the state-machine pattern. The rules share the generated state types and define behavior from their fields. `fromStartMatchesRules` proves agreement on acceptance, the entire next state, and the outcome for every finite sequence of attempted actions.
- Run the verification target to check the proofs and their axiom dependencies. Applying the result to Go execution also relies on the translation preserving Go semantics and on any modeled dependencies satisfying their contracts.

# How to use

Put directives in the relevant declaration's doc comment using the exact `//golean:` prefix.

Choose the home of a law by the behavior it describes:

- **Function or method doc comment** for an operation-specific contract, such as a rejected roll preserving the game. An attached `//golean:verify` selects that operation for translation and declares the law.
- **Concrete type doc comment** for a law about the type across its method set, such as an invariant preserved by every game action.
- **Package doc comment** for a law about the package's behavior across entry points, such as every bowling history from `Start` agreeing with the reference rules.

For type and package laws, select the operations with `//golean:export` or an operation-specific `//golean:verify`. A package law in `doc.go` can import other files' generated models and refer to their qualified Lean names.

Import a handwritten reference specification with `//golean:verify:import` in the package doc comment. Verification laws load after the model, so the specification can use its generated types. Put definitions used by `//golean:assume` in modules loaded through `//golean:assume:import`. Those modules load before the model and must avoid depending on any generated model that uses them.

The [bowling example](../../../examples/provable/bowling/README.md#checked-behavior) demonstrates all three scopes in one package.

| Directive | Placement and use |
| --- | --- |
| `//golean:export` | Function or concrete method. Generate its model without declaring a law. This also makes independent definitions available to laws in the same generated module. |
| `//golean:verify name : proposition` | Function, concrete method, concrete type, or package. Function and method directives also select the operation. Use a unique law name within the Go file. Continue on immediately consecutive `//golean:verify+` lines. |
| `//golean:verify:import Lean.Module` | Package doc comment. Make a Lean module available to verification laws throughout the package. |
| `//golean:assume:import Lean.Module` | Package doc comment. Make a Lean module available to contract propositions, including in generated callers, and to verification laws. |
| `//golean:assume name : proposition` | Named interface or interface method for a contract law. Use one directive line per law. On a concrete callee, declare a law available to callers that explicitly abstract it. Names on concrete callees are unique within the declaration, and consecutive `//golean:assume+` lines continue the proposition. |
| `//golean:abstract Callee` | Caller with a named verification law. Abstract a direct, statically resolved call using `Function`, `Type.Method`, or an import-qualified form. See the limits below. |
| `//golean:assume:initialized` | Named interface field in a service or other record used by verified value methods or functions. The proof assumes a valid dependency satisfying its contract, including exclusion of nil and typed-nil handles. Use annotated fields through values. |
| `//golean:verify:constructor` | Value-returning function that initializes annotated fields directly from same-type interface parameters on each return path. Generates a checked `Function$initialized` theorem for present inputs. Go callers still need valid dependencies and the Go zero value remains constructible. |
| `//golean:boundary Interface.Method readonly` or `//golean:boundary Interface.Method effect` | Root with a named verification law. Use `pkg.Interface.Method` for an imported interface. Classify each interface call in the checked call tree, including calls in helpers. Every entry must be used. |

Concrete call abstraction requires non-generic, non-variadic caller and callee signatures with supported scalar arguments and one scalar result each. Methods require scalar value receivers. Callers that lower to loop helpers or use recursion fuel are outside this subset. Abstraction applies per caller and requires a callee with named assumed or verified laws. In the assumed law, refer to the operation by its unqualified name and supply the receiver first for a method. An assumption-only declaration generates no module by itself. When all abstracted callees have eligible checked proofs, go-lean can specialize the caller theorem with those implementations. See [abstract calls in the README](../../../README.md#abstract-calls-and-assumed-laws).

Boundary classification keeps the Go signature and pairs the usual Lean result with a `List String` trace. Each `effect` call adds `import/path.Interface.Method` in execution order, including repeated calls. A `readonly` call adds no entry and assumes its implementation has no externally observable effects. Interface contracts must describe the return values throughout the sequence. This mode requires an acyclic, total model and rejects any path where a `readonly` call follows an effect, including across helper calls. Callbacks, opaque calls, concrete call abstraction, and constructor verification are outside this mode.

Edit the Go source and directives and `<stem>_proofs.lean`. Generation writes `<stem>_gen.lean` for translated operations and `<stem>_verify.lean` for named laws. A verification import or a type or package law puts the declarations in `<stem>_laws.lean`. The proof companion imports that module when present and imports `<stem>_gen.lean` otherwise. Use the law declaration's namespace followed by `.Proofs` for handwritten theorems. Transpilation maintains generated roots and required proof companion roots in managed Lake blocks. Keep handwritten reference modules and standalone proofs in the manual portion of the roots array. When moving a proof companion, update its module imports and namespace.

Regenerate after Go edits. On a subset error, start with the reported source location and inspect the marked root's reachable calls using the [supported subset](../../../README.md#supported) and [rejection fixtures](../../../examples/reject). After generation succeeds, inspect the model signature before writing the law. Check receiver arguments, contract parameters, result products, modeled panic outcomes, and traces. Build the verification target to catch missing or mismatched theorems and unapproved axiom dependencies. Resolve those errors in the law or handwritten proof, including any use of `sorry` or custom axioms.

# go-lean idiomatic Go

go-lean works best with a rich domain model. Put most business rules on the entities whose state they govern, and keep those methods free of external side effects. In [Nine Men's Morris](../../../examples/provable/nine_mens_morris/morris.go), the public action methods enforce the rules and return the complete next game value. Callers handle persistence and I/O.

Start with a property callers rely on, such as preserving a bound, rejecting an invalid input, or maintaining an invariant after an update. Put operation-specific laws on the public functions and methods callers use. State input preconditions callers can establish and prove the property across the relevant inputs and branches.

Prove internal behavior separately when it helps establish a public law or supplies a useful invariant. If go-lean cannot model a public entry point, report the exact blocker and which observable behavior a narrower proof would cover before proposing that change.

- Prefer explicit inputs, small functions, value structs, and straightforward branches. Keep state local where possible. Read slices and maps without mutating caller-owned storage. Build a fresh result when ownership matters. Favor supported counted loops or slice traversals and make the bound evident. For an in-place operation that fits the API, keep mutation within one tracked receiver and state what changes and what is preserved. See [batch fulfillment](../../../examples/provable/batch_fulfillment/batch_fulfillment_proofs.lean) for a bounded state update.
- Read maps with integer keys and values using `m[k]` or comma-ok lookup. The checker rejects map `range` loops and `len(m)`. See [supported map operations](../../../README.md#supported).
- For fixed-size entity state, use an array field and update the value receiver's copy. Keep element addresses local and guard dynamic indices. Read-only slice fields support whole-field replacement, `len`, nil checks, and checked indexing. Their Lean model preserves nil separately from an empty slice. See the [Morris board](../../../examples/provable/nine_mens_morris/morris.go) for guarded array updates.
- Use the generated types to write the law. Go integer arithmetic wraps at the modeled width, and `int` and `uint` depend on the Go target. If wrapping would break the property, prove it cannot occur under the relevant preconditions. For indexing, division, or nil dereference, use guards or explicit preconditions and prove a successful result where needed. See [guarded division](../../../examples/provable/division_guarded/division_guarded_proofs.lean).
- Keep I/O, time, randomness, and concurrency at natural boundaries. Pass a value into the core when the rule only needs an observation. Use a small named Go interface when the core genuinely calls a dependency. Give the port the laws the caller needs and check that real implementations satisfy them. If a database or network call can fail, keep error handling in the ordinary Go flow and verify the decision that uses the successful observation. The [key-value store implementation](../../../examples/provable/kv_store_contract_impl/kv_store_contract_impl_proofs.lean) shows how translated Go code can discharge an interface contract.
- Use an effect trace when the property is about invoking an operation. In [fraud withdrawal](../../../examples/provable/fraud_withdrawal/fraud_withdrawal_proofs.lean), rejection produces an empty modeled trace and approval invokes the balance setter once. Applying these results requires valid dependencies, their return-value contracts, and honest read-only classifications. The [Go tests](../../../examples/provable/fraud_withdrawal/fraud_withdrawal_test.go) exercise persistence. Transaction and concurrency guarantees belong at the storage or orchestration boundary.
- Use concrete `abstract` with `assume` only as a last resort for unsupported code. First try passing in its result, simplifying it to supported Go, or proving a compatible implementation. For assumptions that remain, state the narrow law and record why the actual callee returns normally, behaves deterministically over the modeled execution, and has no caller-observable effects beyond its return value. Keep the checked claim conditional until the implementation evidence establishes those requirements. See [assumed quota](../../../examples/provable/assumed_quota/assumed_quota.go).
