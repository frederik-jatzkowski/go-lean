# Supported Go

An export, verification law, or enum directive selects the whole package. Concrete modeled dependencies follow the same rules. Every build-selected production declaration must follow the subset, including unused helpers. Use private data types and fields, immutable local initializers, fully keyed value literals, conditionals, early returns, and one unnamed result per function or method. Go tests and separate runtime packages can use ordinary Go.

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

For recursion that needs an explicit measure, supply a Lean `Nat` expression in scope of the entry parameters. Examples include a guarded unsigned countdown and the size of a boxed self-recursive record. See [writing modeled Go](writing-go.md).

## Generated enums

Declare an enum in a package doc comment with `//golean:generate:enum expr { constant, add }`. Each variant is a private struct in the same package. Variant fields can use supported types and refer to the enum itself or another enum. Use `lean.Array` or `lean.List` for variable-length child lists.

`transpile` and `verify` generate `lean.gen.go`. Commit the generated Go file so ordinary Go commands can build the package. Ordinary callers construct values with `Expr_Constant` and `Expr_Add`. Mark a private function such as `eval` with `//golean:export` to generate the checked Go entry point `Eval`. An enum's Go zero value is invalid and checked entry points reject it.

A modeled function can use `MatchExpr` with inline callbacks or an exhaustive native type switch over `e.variant`. Each case uses a value variant. Recursive enum matches can use Lean structural termination or a declared termination measure.

See the [recursive expression example](../examples/proven/recursive_expr/README.md).

## Patterns outside the subset

Raw slices and maps, pointers, interfaces, function values, reassignments, raw Go loops, ordinary switches and user-defined generics are outside the modeled subset. Generated enum matches and structurally recursive enum functions are exceptions to the general restrictions on matching and recursion. Receiver support covers concrete value methods. Pointer receivers, implicit dereferences, promoted methods, and stored method values are outside that support.

Use the reported Go location to identify code that needs a modeled representation or belongs in a runtime package. The [grid game](../examples/proven/grid_game/README.md) shows a runtime driver calling a modeled step, and the [compiler](../examples/proven/stack_machine_compiler/README.md) shows raw bytes converted at the boundary.
