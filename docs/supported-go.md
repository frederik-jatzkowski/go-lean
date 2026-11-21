# Supported Go

go-lean checks the operations you select and their reachable calls under the active Go build settings. Support depends on the types, control flow, and ownership of the values involved. The linked examples show shapes accepted by the checker.

## Data types and results

| Go feature | Lean model |
| --- | --- |
| Booleans and integers | Fixed-width signed and unsigned types preserve Go wraparound. `int` and `uint` follow the Go target and are exposed as `GoTypes.Int` and `GoTypes.UInt`. Named integer types use their underlying representation, including the `byte` and `rune` aliases. Runtime integer casts preserve extension and truncation. |
| Integer arithmetic | Arithmetic includes `+`, `-`, `*`, `/`, and `%`, as well as integer `min` and `max`. Signed division truncates toward zero and a nonzero signed remainder has the dividend's sign. A zero divisor produces a modeled panic. |
| Strings | Lean `ByteArray` represents raw bytes. Supported operations include concatenation, equality, byte length, and two-index slicing. Invalid slice bounds produce a modeled panic. |
| Floating point | Runtime `float32` addition uses binary32 arithmetic. `float64` supports IEEE 754 comparisons, including unordered NaNs and equal signed zeros. Write Go equality laws with Boolean equality, such as `(x == y) = true`. Typed constants preserve their rounded bit representation. |
| Built-in `error` | Supports nil, forwarding, nil checks, and boxing a named zero-field concrete error type. The model records the concrete type identity and distinguishes an error return from a panic outcome. |

Multiple results form a right-nested product in declaration order. For example, `(int64, bool, uint8)` becomes `Int64 × (Bool × UInt8)`. For fallible operations such as unchecked indexing, a possible nil dereference, or runtime integer division, the model uses an outer `Option` around the result, with `none` representing a modeled panic. This outcome propagates to checked callers even if they discard the result.

Examples cover [machine-width integers](../examples/provable/machine_words/machine_words.go), [floating-point comparisons](../examples/provable/float64_special/float64_special.go), [byte strings](../examples/provable/string_bytes/string_bytes.go), [multiple results](../examples/provable/multi_result/multi_result.go), and [division panic propagation](../examples/provable/division_propagation/division_propagation.go).

## Collections and records

- **Structs and arrays.** Named structs with supported fields become Lean structures. Promoted fields follow the embedding path. Unnamed arrays use fixed-length vectors. Local records and arrays and value-receiver copies can be updated while field and element addresses stay local. Dynamic indices need bounds checks unless the checker can establish safety. [Array bounds](../examples/provable/array_bounds/array_bounds.go)
- **Slices.** Read-only slices support length and indexing. Slice fields allow nil checks and whole-field replacement. Check the generated signature before writing a law. Depending on the operations and module, the model can use a list, an optional list to distinguish nil from empty, or an optional list and capacity pair. [Slice bounds](../examples/provable/slice_bounds/slice_bounds.go) and [expression parser](expression-parser.md)
- **Fresh slices.** Supported builders include copying matching elements, filling an input-sized slice once per index, and appending at most one element per iteration of a slice range to an empty local slice preallocated to the input length. The allocation must stay local until return. Capacity-tracked slices support `cap`, and fresh append folds require a module without stateful receiver methods. [Slice copy](../examples/provable/slice_copy/slice_copy.go), [generic map](../examples/provable/generic_map/generic_map.go), and [filter and count](../examples/provable/filter_and_count/filter_and_count.go)
- **Maps.** String or integer keys with integer values support lookup and comma-ok lookup. A missing key returns the value's zero value. The checker rejects map iteration and `len(m)`. A fresh local map can be built and returned through supported acyclic control flow. One supported loop pattern builds a filtered string slice and a fresh map of counts. [Map lookup](../examples/provable/map_lookup/map_lookup.go) and [map construction](../examples/provable/map_build/map_build.go)

## Control flow and calls

- **Branches.** Local assignments, early returns, short-circuit expressions, and value and tagless switches are supported.
- **Bounded loops.** Write at most one loop per function. Range over a modeled slice or array, or use a counted loop that advances by one while the counter is below an invariant upper bound. Use integers and booleans for ordinary loop-carried state. An iteration can branch, advance, continue, break to the code after the loop, or return from the function. Checked operations in the body keep their modeled panic behavior. [Bounded counter](../examples/provable/bounded_counter/bounded_counter.go) and [loop exits](../examples/provable/instruction_fold/control.go)
- **Composing loops.** Extract a second or nested traversal into a checked helper and pass the accumulator as an argument. Each helper may have its own bounded loop, and the call graph for this composition must be acyclic. A read-only slice field can be passed to a helper or ranged over directly inside it. Ranging over a nil slice performs zero iterations. [Verified helper calls](../examples/provable/instruction_fold/instruction_fold.go)
- **Concrete calls and generics.** Direct calls may cross package boundaries when the Go body is available and supported. Generic definitions support unconstrained `any` parameters and checked concrete instances. Direct local closure calls support immutable captures, including statically known callbacks used by supported fresh-slice builders. [Imported clamp helpers](../examples/provable/clampimport/clampimport.go), [generic map](../examples/provable/generic_map/generic_map.go), and [immutable closure](../examples/provable/immutable_closure/immutable_closure.go)
- **Pointer inputs and recursion.** Read-only pointers to nonrecursive records use `Option` to model nil. A specific nil-guarded recursion pattern follows a linked input with integer payloads and lowers to structural recursion. Applying that proof requires a finite, acyclic chain. [Nil dereference](../examples/provable/nil_dereference/nil_dereference.go) and [acyclic list](../examples/provable/acyclic_list/acyclic_list.go)
- **Interface calls.** Named interfaces with explicit contracts become Lean structures containing method models and laws. A method can return a single supported value or a handle of the same interface. A void method uses `Unit`. Classified boundaries can also return a trace of effect calls. [Dependency contracts](verification.md#model-a-dependency) and [order service](order-service.md)

## Receiver mutation

Supported pointer-receiver methods can mutate one tracked record through direct field assignments and checked same-receiver helpers. Slice fields are read-only at the element level and the model can track whole-field updates, nilness, and supported `slices.Clone` calls. The bounded loop pattern advances a receiver cursor once per continuation while it is below the length of a receiver slice. The result is `Option (Option Receiver × Result)`. The outer option models a panic and the inner option models a nil receiver.

A supported variant takes one directly called, non-nil unary Boolean callback with a scalar argument. The model supplies responses by invocation index and argument, and reports the arguments in order on normal return. Applying a theorem requires the callback to return normally and leave the receiver and all slice storage read by the invocation untouched. [Movement arrival](../examples/provable/movement_arrival/movement_arrival_proofs.lean) and [batch fulfillment](../examples/provable/batch_fulfillment/batch_fulfillment_proofs.lean)

## Common rejections

Mutable globals, writes to caller-owned slices or maps, escaping aliases, arbitrary indirect calls, unsupported loop and recursion shapes, reflection, and goroutines are examples of operations the checker can reject. Start from the reported Go location and follow the reachable calls from your selected root. [Rejection fixtures](../examples/reject)
