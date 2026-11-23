# Toy compiler language specification

Compile ASCII source into stack bytecode, then execute that bytecode one instruction at a time. The compiler splits the work into four passes. Tokenization finds lexemes and byte offsets. Parsing builds an expression tree. Type checking assigns a type to each node. Emission encodes the tree for a VM whose stack holds raw bytes.

```sh
go run ./examples/provable/stack-machine-compiler/cmd/toy-compiler "and eq add 255 1 0 not false"
go test ./examples/provable/stack-machine-compiler/...
go run ./cmd/go-lean verify ./examples/provable/stack-machine-compiler
```

The example evaluates to `true`. It checks that adding one to 255 wraps to zero and that negating false produces true.

## Source language

A program is one prefix expression. ASCII space, tab, carriage return, and newline separate tokens. Leading and trailing whitespace are accepted. Decimal literals range from 0 to 255, with no leading zeroes other than `0`. Keywords are lowercase.

| Expression | Operand types | Result |
| --- | --- | --- |
| `0` through `255` | | `U8` |
| `true`, `false` | | `Bool` |
| `add x y`, `sub x y` | `U8`, `U8` | `U8`, arithmetic modulo 256 |
| `eq x y`, `lt x y` | `U8`, `U8` | `Bool` |
| `and x y` | `Bool`, `Bool` | `Bool`, eager conjunction |
| `not x` | `Bool` | `Bool` |

Source, tokens, bytecode, and the live operand stack are variable-sized. Diagnostics carry zero-based byte offsets. The first invalid word reports its start. Missing operands and extra expressions report the original end of input. Type errors report the offending operator, visiting right children before left children and checking children before their parent. After type checking, the compiler reports `CodeTooLarge` at EOF if the encoded program would exceed Go’s maximum slice length.

## Follow the passes

1. The tokenizer records each token's kind, literal value, and start offset. It also retains the source end offset so the parser can report EOF after trailing whitespace.
2. The parser scans tokens right to left. A literal adds a leaf. An operator consumes the required number of subtree roots and adds a parent. This stores the tree in right-first postorder, with child indices smaller than their parent. After type checking, the compiler reports `CodeTooLarge` at EOF if the encoded program would exceed Go’s maximum slice length.
3. The type checker visits nodes in that stored order, reads each child's inferred type, and checks the operator signature. For example, `add true 1` parses and produces a type error at byte zero.
4. The emitter uses the same node order to emit one instruction per node, followed by `Halt`. The right operand goes onto the stack first, so the left operand is on top when evaluating subtraction or less-than.

Each instruction takes two bytes. The first is the opcode. `Push` uses the second as its immediate. The emitter writes zero as the second byte for other instructions. The VM ignores those reserved bytes.

| Opcode | Instruction |
| --- | --- |
| 0 | Halt |
| 1 | Push |
| 2 | Add |
| 3 | Sub |
| 4 | Eq |
| 5 | Lt |
| 6 | And |
| 7 | Not |

`Compile` returns exactly the emitted bytes. `Run(code)` starts with an empty stack. `Step(code, state)` takes a byte-offset PC and a slice of live operands, with the top at the end. Every opcode needs a complete pair. An odd PC, truncated pair, or fetch past EOF reports `InvalidPC` before opcode decoding. Unknown opcodes report `InvalidOpcode`. Operand underflow and a push at maximum representable stack length report `InvalidStack`. Halt and faults preserve the input state. Raw Boolean instructions treat nonzero bytes as true and produce canonical bytes, `0` or `1`. The compiler's static type information determines how a caller interprets the final byte.

## Lean specification

[spec.lean](../examples/provable/stack-machine-compiler/spec.lean) defines the
lexical grammar, prefix expressions, typing and evaluation, compilation
diagnostics, and bytecode execution. Its `Requirements` namespace connects
those rules to the generated model:

- `compilationConforms` requires a specified outcome for every source and
  checks diagnostics, the result type, and the exact emitted bytes.
- `stepConforms` checks instruction effects and fault precedence.
- `executionConforms` requires execution to stop at the first halt or fault
  within `len(code)/2 + 1` steps.
- `preservesSourceMeaning` requires compiled programs to halt with a single
  stack byte representing the typed source value.

The Go package registers these requirements together as `Laws.all`.
`lake build +compiler` type-checks the generated law.
`go run ./cmd/go-lean verify ./examples/provable/stack-machine-compiler`
also checks the proof in `compiler_proofs.lean`, which is still pending.
The Go tests exercise variable-size compilation, the public VM, and the CLI.
