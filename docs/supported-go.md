# Supported Go

go-lean checks the call graph reached from exported and verified operations. Ordinary Go at the boundary can use the full language. Within the modeled graph, use immutable local initializers, fully keyed value literals, conditionals, early returns, and one unnamed result per function or method.

## Types and operations

| Go | Lean and behavior |
| --- | --- |
| Booleans and comparisons | Lean Boolean values. Laws can state propositions about their results. |
| Fixed-width integers | Signed or unsigned Lean machine integers. Addition and subtraction wrap at the modeled width. |
| `int`, `uint` | Machine integers at the Go target's width. |
| Strings | Byte sequences with lexicographic comparison. |
| Named value structs | Lean records with fields such as `value.«field:Name»`. |
| `lean.Array[T]`, `lean.ByteArray` | `Array` and `ByteArray`. Out-of-bounds reads return `None`, and out-of-bounds updates preserve the input. |
| `lean.List[T]`, `lean.Option[T]` | `List` and `Option`. |
| `lean.OrderedMap[K,V]`, `lean.OrderedSet[K]` | `Std.TreeMap` and `Std.TreeSet`. |
| `lean.Box[T]` | `Option`. Reading an empty box with `Get()` returns the modeled Go zero value. |
| `lean.BitVec` | A width paired with a bit vector of that width. Widths above 64 yield `None`. Index zero is the least significant bit. |

Empty curated collection literals model empty collections. Updates preserve earlier values. Byte extraction clamps half-open bounds. Use `lean.ByteArrayFromBytes` to copy a Go slice at the boundary. When applying a Lean statement over arbitrary collection sizes to Go, account for the lengths representable by Go's `int`.

## Calls and traversal

Direct calls resolve statically. Concrete value-receiver calls and method expressions translate with the receiver first. A modeled invocation of `board.stoneAt(point)` calls `«Board$stoneAt»` in Lean. For concrete calls across packages, mark the callee with `//golean:export`.

| Helper | Step signature | Visits |
| --- | --- | --- |
| `lean.FoldN(n, seed, step)` | `func(uint, S) S` | Indices from zero through `n-1` |
| `lean.FoldNUntil(n, seed, step)` | `func(uint, S) lean.FoldControl[S]` | The same indices until the step stops |
| `lean.FoldList(items, seed, step)` | `func(T, S) S` | List items from the head |
| `lean.FoldListUntil(items, seed, step)` | `func(T, S) lean.FoldControl[S]` | List items from the head until the step stops |

Pass a directly named non-generic function. Empty traversals make no step calls. The early-stop result carries the stopping step's state and flag, including a stop on the last visit. Exhaustion returns the final state with a false flag. Lean models the state and flag as `S × Bool`. The generated count equations recurse on the remaining count, and the list equations unfold on empty and cons cases.

For direct recursion, supply a Lean `Nat` measure in scope of the entry parameters. Use a guarded unsigned countdown or a boxed self-recursive record with a decreasing size measure. See [writing modeled Go](writing-go.md).

## Patterns outside the subset

Raw slices and maps, pointers, interfaces, function values, reassignments, raw Go loops, switches, user-defined generics, and unannotated or mutual recursion are outside the modeled subset. Receiver support covers concrete value methods. Pointer receivers, implicit dereferences, promoted methods, and stored method values are outside that support.

When translation reports a Go location, trace the call from the marked operation and decide which values should cross the model boundary. The [grid game](../examples/proven/grid_game/README.md) shows a runtime driver calling a modeled step, and the [compiler](../examples/proven/stack_machine_compiler/README.md) shows raw bytes converted at the boundary.
