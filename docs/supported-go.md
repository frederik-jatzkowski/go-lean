# Supported Go

go-lean checks the operations you select and their reachable calls under the active Go build settings. Support depends on the types, control flow, and ownership of the values involved. The linked examples show shapes accepted by the checker.

## Writing Go for verification

Start with a caller-visible property and give it a named verification law. State the result, state change, rejection, or effect the caller relies on. Keep the expected behavior independent of the implementation and include the relevant failure paths. [Write a law](verification.md)

### Keep writes local

Use value receivers for domain transitions that return the next state and a domain result. A value receiver lets you change scalar fields, embedded value records, and array elements on its copy. Slice and map fields can still share storage with the caller. Read borrowed collection elements and allocate fresh storage for writes. Use the [tracked receiver model](#receiver-mutation) when in-place receiver updates are part of the API.

Allocate a fresh builder before its loop and keep one current mutable storage view. Finish writes before publishing the collection through a helper call or another aggregate, then return the finished value. For append, use the returned view for subsequent operations:

```go
func FilterPositive(in []int64) []int64 {
	out := make([]int64, 0, len(in))
	for _, x := range in {
		if x > 0 {
			out = append(out, x)
		}
	}
	return out
}
```

The checker works on SSA values. Two source names can denote the same view. Keeping `previous := out` and reading `len(previous)` after `out = append(out, x)` keeps the old view live and is rejected. [Verified collection builders](../examples/provable/owned_collection/owned_collection.go)

### Compose bounded traversals

Use at most one supported bounded loop per function. Extract nested or sequential traversals into directly called checked helpers. Pass the current accumulator to the helper when the outer proof needs to preserve the order of updates. Supply an explicit ordered key slice for map traversal. Go leaves map iteration order unspecified. [Verified instruction folds](../examples/provable/instruction_fold/instruction_fold.go)

For a signed index, check both `0 <= i` and `i < len(s)`, or establish those facts in the proof. Model failure explicitly where it matters. A zero divisor can panic, while ordinary integer overflow wraps at the modeled width. State and prove an overflow bound when the law depends on mathematical arithmetic. [Array bounds](../examples/provable/array_bounds/array_bounds.go) and [guarded division](../examples/provable/division_guarded/division_guarded.go)

### Keep dependency contracts explicit

Pass observations such as a timestamp as values when the rule only needs their contents. When the operation itself calls storage or another dependency, use a small named interface with `//golean:assume` laws for the needed return values. Add a named verification law and classify the reachable interface calls with `//golean:boundary` when the law concerns effects. The trace records effect calls in order, including repeats. Along each path, read-only calls must precede effects. The [checked order service](../examples/provable/order_service/orders.go) shows the domain transition, initialized repository field, and persistence law together.

## Data types and results

| Go feature | Lean model |
| --- | --- |
| Booleans and integers | Fixed-width signed and unsigned types preserve Go wraparound. `int` and `uint` follow the Go target and are exposed as `GoTypes.Int` and `GoTypes.UInt`. Named integer types use their underlying representation, including the `byte` and `rune` aliases. Runtime integer casts preserve extension and truncation. |
| Integer arithmetic | Arithmetic includes `+`, `-`, `*`, `/`, and `%`, as well as integer `min` and `max`. Signed division truncates toward zero and a nonzero signed remainder has the dividend's sign. A zero divisor produces a modeled panic. |
| Strings | Lean `ByteArray` represents raw bytes. Supported operations include concatenation, equality, byte length, two-index slicing, and `[]byte(s)` conversion. Invalid slice bounds produce a modeled panic. |
| Floating point | Runtime `float32` addition uses binary32 arithmetic. `float64` supports IEEE 754 comparisons, including unordered NaNs and equal signed zeros. Write Go equality laws with Boolean equality, such as `(x == y) = true`. Typed constants preserve their rounded bit representation. |
| Built-in `error` | Supports nil, forwarding, nil checks, and boxing a named zero-field concrete error type. The model records the concrete type identity and distinguishes an error return from a panic outcome. |

Multiple results form a right-nested product in declaration order. For example, `(int64, bool, uint8)` becomes `Int64 × (Bool × UInt8)`. For fallible operations such as unchecked indexing, a possible nil dereference, or runtime integer division, the model uses an outer `Option` around the result, with `none` representing a modeled panic. This outcome propagates to checked callers even if they discard the result.

Examples cover [machine-width integers](../examples/provable/machine_words/machine_words.go), [floating-point comparisons](../examples/provable/float64_special/float64_special.go), [byte strings](../examples/provable/string_bytes/string_bytes.go), [multiple results](../examples/provable/multi_result/multi_result.go), and [division panic propagation](../examples/provable/division_propagation/division_propagation.go).

## Collections and records

- **Structs and arrays.** Named structs with supported fields become Lean structures. Promoted fields follow the embedding path. Unnamed arrays use fixed-length vectors. Local records and arrays and value-receiver copies can be updated while field and element addresses stay local. Dynamic indices need bounds checks unless the checker can establish safety. [Array bounds](../examples/provable/array_bounds/array_bounds.go)
- **Slices.** Read-only slices support length and indexing. Slice fields allow nil checks and whole-field replacement. Check the generated signature before writing a law. Depending on the operations and module, the model can use a list, an optional list to distinguish nil from empty, or an optional list and capacity pair. [Slice bounds](../examples/provable/slice_bounds/slice_bounds.go) and [expression parser](expression-parser.md)
- **String to byte slice.** `[]byte(s)` produces a fresh, non-nil slice with the string's raw bytes in order. The result follows the fresh collection rules below. Observing byte-slice capacity in the same generated call graph is unsupported with this conversion. [Checked byte preservation](../examples/provable/string_bytes/string_bytes.go)
- **Fresh slices.** Supported builders include copying matching elements, filling an input-sized slice once per index, and appending at most one element per iteration of a slice range to an empty local slice preallocated to the input length. The allocation must stay local until return. Capacity-tracked slices support `cap`, and fresh append folds require a module without stateful receiver methods. [Slice copy](../examples/provable/slice_copy/slice_copy.go), [generic map](../examples/provable/generic_map/generic_map.go), and [filter and count](../examples/provable/filter_and_count/filter_and_count.go)
- **Maps.** String or integer keys with integer values support lookup and comma-ok lookup. A missing key returns the value's zero value. The checker rejects map iteration and `len(m)`. To build a map in a bounded loop, traverse an ordered input slice and update a fresh local map. [Map lookup](../examples/provable/map_lookup/map_lookup.go) and [verified builders](../examples/provable/owned_collection/owned_collection.go)
- **Fresh local collections.** Allocate a slice or map before the loop, populate it through one live mutable view, and return it. Branches can skip or repeat writes, and the model preserves bounds panics for indexed writes. Putting the collection into another aggregate or passing it to a helper makes it read-only for the rest of the function. Later writes report `cannot write collection after publication`. Keep element addresses local to their accesses. Append consumes the previous view. When slice capacity is observed, append requires the supported preallocated fold. [Verified builders](../examples/provable/owned_collection/owned_collection.go)

## Control flow and calls

- **Branches.** Local assignments, early returns, short-circuit expressions, and value and tagless switches are supported.
- **Owned receiver buffers.** A checked pointer-receiver method can initialize distinct slice fields with fresh `make` allocations sized from inputs, append single elements back to their source field, and update indexed elements or fields of record elements. Same-receiver helpers inherit ownership from the calling method. Every checked entry point must establish ownership before its first write. Lean uses optional `Array` fields, preserving nil and checking allocation and indexing bounds. Capacity can size an allocation, while observing a buffer with `cap`, publishing its slice or element addresses, and invoking callbacks during the transition are outside the supported subset. [Owned buffer builder](../examples/provable/owned_buffer/builder.go)
- **Bounded loops.** Write at most one loop per function. Range over a modeled slice or array, or use a counted loop that advances by one while the counter is below an invariant upper bound. Carry integers, booleans, fresh local collection state, or fixed arrays allocated before the loop whose addresses stay local. A checked helper can receive the current array by value, and the caller can keep updating its local array afterward. An iteration can branch, advance, continue, break to the code after the loop, or return from the function. Checked operations in the body keep their modeled panic behavior. [Bounded counter](../examples/provable/bounded_counter/bounded_counter.go) and [loop exits](../examples/provable/instruction_fold/control.go)
- **Composing loops.** Extract a second or nested traversal into a checked helper and pass the accumulator as an argument. Each helper may have its own bounded loop, and the call graph for this composition must be acyclic. A read-only slice field can be passed to a helper or ranged over directly inside it. Ranging over a nil slice performs zero iterations. [Verified helper calls](../examples/provable/instruction_fold/instruction_fold.go)
- **Concrete calls and generics.** Direct calls may cross package boundaries when the Go body is available and supported. Generic definitions support unconstrained `any` parameters and checked concrete instances. Direct local closure calls support immutable captures, including statically known callbacks used by supported fresh-slice builders. [Imported clamp helpers](../examples/provable/clampimport/clampimport.go), [generic map](../examples/provable/generic_map/generic_map.go), and [immutable closure](../examples/provable/immutable_closure/immutable_closure.go)
- **Pointer inputs and recursion.** Read-only pointers to nonrecursive records use `Option` to model nil. A specific nil-guarded recursion pattern follows a linked input with integer payloads and lowers to structural recursion. Applying that proof requires a finite, acyclic chain. [Nil dereference](../examples/provable/nil_dereference/nil_dereference.go) and [acyclic list](../examples/provable/acyclic_list/acyclic_list.go)
- **Measured recursion.** Add `//golean:decreases n.toNat` alongside `//golean:export` or `//golean:verify` to give a directly recursive function a Lean `Nat` measure. The measure uses the Go entry parameter names. Each recursive call must decrease it relative to that invocation's entry values. The model uses `Option` for the result and exposes Lean's `.eq_def` unfolding theorem. Measured functions support multiple calls and can pass a previous result into a later call. Mutating receivers, mutual recursion, generic recursion, and loops inside a measured function are outside the supported subset.
- **Interface calls.** Named interfaces with explicit contracts become Lean structures containing method models and laws. A method can return a single supported value or a handle of the same interface. A void method uses `Unit`. Classified boundaries can also return a trace of effect calls. [Dependency contracts](verification.md#model-a-dependency) and [order service](order-service.md)

The model contains a proposition such as `«Count$decrease1»` for each recursive path. The proposition includes the dominating branch guards and compares the callee's measure with the caller's entry measure. Results of preceding calls and checked operations are quantified in these propositions. If automatic discharge fails, add `<package>_decreases_proofs.lean`, import the `<package>_decreases.lean` module generated when the companion exists, and prove the proposition in `GoLean.«your/go/import/path».Decreases` under the same theorem name. Proofs and recursive definitions are checked for unapproved axioms.

## Receiver mutation

Supported pointer-receiver methods can mutate one tracked record through direct field assignments and checked same-receiver helpers. Slice fields are read-only at the element level and the model can track whole-field updates, nilness, and supported `slices.Clone` calls. The bounded loop pattern advances a receiver cursor once per continuation while it is below the length of a receiver slice. The result is `Option (Option Receiver × Result)`. The outer option models a panic and the inner option models a nil receiver.

A supported variant takes one directly called, non-nil unary Boolean callback with a scalar argument. The model supplies responses by invocation index and argument, and reports the arguments in order on normal return. Applying a theorem requires the callback to return normally and leave the receiver and all slice storage read by the invocation untouched. [Movement arrival](../examples/provable/movement_arrival/movement_arrival_proofs.lean) and [batch fulfillment](../examples/provable/batch_fulfillment/batch_fulfillment_proofs.lean)

## Common rejections

Keep mutable globals, concurrent operations such as goroutines or channel communication, unsafe pointer operations, reflection, and deferred cleanup in orchestration outside the checked call tree. The checker also rejects writes to caller-owned slice or map storage, escaping aliases, stored function values, and unsupported loop or recursion shapes. Start from the reported Go location and follow the reachable calls from your selected root. [Rejection fixtures](../examples/reject)
