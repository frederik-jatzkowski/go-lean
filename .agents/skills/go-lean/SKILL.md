---
name: go-lean
description: Write and verify strict Go models with go-lean, use curated Lean-like values, and prove package laws over generated Lean definitions.
---

# Verify a Go package

Use Go 1.26 or later and install Elan. Run commands from the Go module root. In a consuming module, install the tool and initialize its workspace:

```sh
go get -tool github.com/frederik-jatzkowski/go-lean/cmd/go-lean@latest
go tool go-lean setup
go tool go-lean doctor
go tool go-lean transpile ./pkg
go tool go-lean verify ./pkg
```

In the go-lean repository, use `go run ./cmd/go-lean` in place of `go tool go-lean`. The pinned toolchain is Lean 4.36.0. Use `.`, `./pkg`, `./pkg/...`, or `./...` for package selection. A selected package outside the managed Lake source directories needs a `lean_lib` with a local `srcDir` and a managed roots block. Keep manually maintained roots outside the block. The archived examples live in a separate Go module under `examples/legacy`.

# Write the modeled Go

Separate pure, total decision logic from I/O and other runtime behavior. Every modeled Go function has one unnamed result and a statically resolved call graph. Use named value structs with fully keyed literals, explicit immutable local initializers, `if`, early returns, scalar comparisons, Boolean operators, and integer addition or subtraction. Use integer constants or typed parameters for inputs. Fixed-width Go arithmetic wraps in Lean, and `int` and `uint` follow the Go target architecture. Strings model raw bytes in lexicographic order.

The modeled graph supports boolean, integer, and string scalars, value structs, and curated types. Pointers, raw slices and maps, interfaces, function values, reassignment, loops, recursion, switches, and user-defined generics are outside the subset. Ordinary Go can use these features outside the modeled graph. Prefer a small state transition a caller can run repeatedly over embedding its driver loop in the model.

Direct calls to user-defined methods on supported concrete value receivers are modeled as functions with the receiver first. This includes `value.Method(args)` and `Type.Method(value, args)`. Refer to the generated method as `«Type$Method»` in Lean laws. Pointer receivers, implicit dereferences, promoted methods, and stored method values are outside the subset. Methods follow the same directive and single-result rules as functions. Name ordinary functions in dependency contracts.

Use the Go package `github.com/frederik-jatzkowski/go-lean/pkg/lean` for values with Lean counterparts:

| Go | Lean |
| --- | --- |
| `Array[T]`, `ByteArray` | `Array`, `ByteArray` |
| `RBMap[K,V]`, `RBSet[K]` | `Std.TreeMap`, `Std.TreeSet` |
| `Option[T]`, `List[T]` | `Option`, `List` |
| `BitVec` | A width at most 64 paired with a `BitVec` of that width |

Empty curated Go literals have empty Lean models. Updates preserve prior versions. Access outside the bounds yields `None`, and out-of-bounds writes preserve the input. Byte extraction uses clamped half-open bounds. `ByteArrayFromBytes` copies a raw Go slice at the boundary. Pass its result into a modeled function. When transferring a Lean statement about arbitrary collection sizes to Go, restrict inputs and intermediates to lengths representable by a Go `int`. Bit indexes count from the least significant bit, and a width above 64 yields `None`.

# Select functions and state laws

Use directives in function doc comments with the exact `//golean:` prefix.

| Directive | Purpose |
| --- | --- |
| `//golean:export` | Model a function and permit concrete calls from other packages. Unmarked local helpers are modeled when reached. |
| `//golean:verify name : proposition` | Model a function and declare a Lean proposition, with a name unique within the package. Continue it on consecutive `//golean:verify+` lines. |
| `//golean:assume name : proposition` | Declare an explicit law about a scalar function. Refer to the operation by its unqualified Go name. Continue it with `//golean:assume+`. |
| `//golean:abstract alias.Function` | In a verified root, replace an explicitly named direct call with a contract parameter. Use the Go import alias or an unqualified local function name. |

An abstract root takes the generated contracts before its ordinary arguments. In its laws, use `dependency0`, `dependency1`, and so on in directive order. Its checked claims are conditional on the runtime callees satisfying those laws. Keep the assumption narrow and state independently what runtime behavior warrants it. See [assumed_worker](../../../examples/provable/assumed_worker/assumed_worker.go).

Concrete cross-package calls use the dependency's generated model. Export each called function and import the dependency's verification module from a handwritten proof to reuse its `Checked` theorems. See [clampimport](../../../examples/provable/clampimport/clampimport_proofs.lean).

# Discharge proof obligations

Generation puts the model and formal laws in `<package>.lean`, with a review copy of the laws at the top. Packages with laws also get separate proof and verification modules. If migrating from a workspace with a separate laws module, update the handwritten companion to import `<package>.lean` before removing the old generated model and laws files. Edit only the handwritten `<package>_proofs.lean` companion. Generation creates it on the first run and preserves it thereafter. Use the namespace `GoLean.«full/go/import/path».Proofs` and one theorem `theorem lawName : Laws.lawName` per obligation. State laws independently of the implementation wherever possible. Verification checks theorem types and axiom dependencies. Replace every scaffold `sorry` with a proof.

For a state machine, prove that the generated step preserves an invariant, then induct on histories from the initial state. Put observations such as accepting a move or reaching a goal in the law. The [grid game proof](../../../examples/provable/grid_game/grid_game_proofs.lean) covers all finite move histories in bounded and wrapping modes. Run verification again after changing a Go implementation or a proof.
