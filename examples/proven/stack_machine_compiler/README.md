# Stack-machine compiler

Compile and run a prefix expression:

```sh
go run ./examples/proven/stack_machine_compiler/cmd/toy-compiler "and eq add 255 1 0 not false"
# Bool: true
```

`add 255 1` wraps to zero, `eq` compares it with zero, and `not false` produces the other true operand of `and`. To see a rejected program, try `add true 1`. It parses, then fails type checking at the operator at byte zero.

A program contains one prefix expression. These are its forms:

| Form | Operand types | Result |
| --- | --- | --- |
| `0` through `255` | | `U8` |
| `true`, `false` | | `Bool` |
| `add x y`, `sub x y` | `U8`, `U8` | `U8`, modulo 256 |
| `eq x y`, `lt x y` | `U8`, `U8` | `Bool` |
| `and x y` | `Bool`, `Bool` | `Bool`, with both operands evaluated |
| `not x` | `Bool` | `Bool` |

## Follow the passes

1. `tokenize` scans source bytes into tokens with their starting offsets. ASCII whitespace separates tokens, and decimal literals range from 0 to 255 with no leading zeros except for `0`.
2. `parse` reads tokens right to left and builds a tree of boxed expressions. An operator takes one or two subtrees from the stack according to its arity.
3. `checkExpression` checks children right before left and then checks the operator. Arithmetic and comparisons take unsigned byte operands. `and` and `not` take Boolean operands.
4. `emitExpression` emits a binary operator's right operand first so the left operand is on top for operations such as subtraction. Instructions are opcode and payload pairs. The compiler appends a final halt.
5. The VM fetches a pair at the byte-offset program counter, checks the instruction and stack, then executes it. The runner stops at the first halt or fault. [Compiler](compiler.go), [VM](vm.go), and [runner](run.go)

## go-lean features

`Compile` copies a Go slice into a modeled `lean.ByteArray`. Scanning, parsing, and VM execution use `FoldNUntil` with named steps. For example, the parser carries its input and partial roots in a value record:

```go
func parse(words lean.Array[lexeme]) lean.FoldControl[parser] {
	initial := parser{Words: words, Roots: lean.Array[expression]{}}
	return lean.FoldNUntil(words.Size(), initial, parseWord)
}
```

Expression children use `lean.Box[expression]`. Both type checking and emission recurse into those children with `//golean:termination:by sizeOf expr`. The package imports `spec` with `//golean:verify:import` and gives the independent requirements the modeled compilation, step, and run functions. [Specification](spec.lean)

## Proof challenge

`Laws.«all»` bundles compilation conformance, instruction-step conformance, execution conformance, and preservation of source meaning. Exact diagnostic precedence is part of compilation conformance. For example, a lexical error must win over errors in later passes, and the type checker visits a binary operator's right child before its left. `compilationCorrect` connects the scanner's first failure and the parser's success or rejection to the specification before considering typing and emission.

The VM has its own precedence rules. A bad instruction address wins over an unknown opcode or stack fault. The step proof checks this ordering as well as stack effects. The run proof relates the early-stopping Go fold to the specification's first halt or fault.

Correct emission also needs a compositional stack argument. `evalSteps` relates evaluation of a typed expression to execution of its emitted instructions in a bytecode context. That result allows the proof to compose the two operand executions with the operator and preserve the stack already present beneath them. `preservesMeaning` combines it with compilation conformance to obtain a halt with a single byte representing the typed source result. The final theorem `«all»` supplies the four proofs. [Lean proofs](compiler_proofs.lean)

```sh
go test ./examples/proven/stack_machine_compiler/...
go run ./cmd/go-lean verify ./examples/proven/stack_machine_compiler
```

Use a 64-bit Go target for this proof. Its size premises use the maximum Go `int` on that target.
