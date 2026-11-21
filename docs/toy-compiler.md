# Verified toy compiler

Compile ASCII source into stack bytecode, then execute that bytecode one instruction at a time. The compiler splits the work into four passes. Tokenization finds lexemes and byte offsets. Parsing builds an expression tree. Type checking assigns a type to each node. Emission encodes the tree for a VM whose stack holds raw bytes.

```sh
go run ./examples/provable/bytecode_vm/compiler/cmd/toy-compiler "and eq add 255 1 0 not false"
go test ./examples/provable/bytecode_vm/compiler/...
go run ./cmd/go-lean verify ./examples/provable/bytecode_vm/compiler
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

The compiler accepts up to 256 bytes and 32 tokens. Diagnostics carry zero-based byte offsets. Inputs longer than 256 bytes fail at offset 256. A bad lexeme reports its start. A valid 33rd token reports its start as a token-limit error. Missing operands and extra expressions report the original end of input. Type errors report the offending operator, visiting right children before left children and checking children before their parent.

## Follow the passes

1. The tokenizer records each token's kind, literal value, and start offset. It also retains the source end offset so the parser can report EOF after trailing whitespace.
2. The parser scans tokens right to left. A literal adds a leaf. An operator consumes the required number of subtree roots and adds a parent. This stores the tree in right-first postorder, with child indices smaller than their parent.
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

The VM checks instruction alignment, program counter bounds, and stack bounds. Raw Boolean instructions treat nonzero bytes as true and produce canonical bytes, `0` or `1`. The compiler's static type information determines how a caller interprets the final byte.

## Read the proofs

Start with the [reference source semantics](../examples/provable/bytecode_vm/compiler/compiler_spec.lean) and the [compiler pass proofs](../examples/provable/bytecode_vm/compiler/compiler_proofs.lean). The [parser refinement](../examples/provable/bytecode_vm/compiler/parse_refinement.lean) connects the array representation to prefix expression trees. The [typing proof](../examples/provable/bytecode_vm/compiler/typing.lean) connects node types to the source typing rules. The [encoding proof](../examples/provable/bytecode_vm/compiler/encoding.lean) relates the complete used bytecode to the reference instruction sequence.

The [stack machine contract](../examples/provable/bytecode_vm/compiler/vm_spec.lean) describes one instruction and its complete state transition, including raw bytecode errors. The [execution proof](../examples/provable/bytecode_vm/compiler/sequencing.lean) uses the generated step model and a subtree lemma that preserves the live stack prefix and pushes the subtree's encoded value. From the empty stack, each compiled expression takes one continuing step per syntax node followed by halt with one live result byte. The Go `Run` wrapper is exercised by tests.

The [source-to-execution proof](../examples/provable/bytecode_vm/compiler/source_execution.lean) composes these results. It checks that the generated compiler returns the reference pipeline's first diagnostic or its exact compiled artifact, and that successfully compiled code halts with the reference expression value. The source laws quantify over byte lists whose length fits a Go `int`, as it does for every actual Go slice.
