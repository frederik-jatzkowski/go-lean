/-!
Observable requirements for the toy source language and its bytecode.
The syntax and semantics use source trees and stack effects. Generated definitions
are supplied by the package law through the observable interfaces below.
-/
namespace StackMachineCompiler.Spec

inductive Ty where
  | u8 | bool
  deriving DecidableEq

inductive Value where
  | number (n : UInt8)
  | boolean (b : Bool)

def Value.ty : Value → Ty
  | .number _ => .u8
  | .boolean _ => .bool

def boolByte (b : Bool) : UInt8 := if b then 1 else 0

def Value.byte : Value → UInt8
  | .number n => n
  | .boolean b => boolByte b

inductive BinOp where
  | add | sub | eq | lt | and

def BinOp.keyword : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .eq => "eq"
  | .lt => "lt"
  | .and => "and"

def BinOp.signature : BinOp → Ty × Ty
  | .add | .sub => (.u8, .u8)
  | .eq | .lt => (.u8, .bool)
  | .and => (.bool, .bool)

def BinOp.eval : BinOp → Value → Value → Option Value
  | .add, .number l, .number r => some (.number (l + r))
  | .sub, .number l, .number r => some (.number (l - r))
  | .eq, .number l, .number r => some (.boolean (l == r))
  | .lt, .number l, .number r => some (.boolean (decide (l < r)))
  | .and, .boolean l, .boolean r => some (.boolean (l && r))
  | _, _, _ => none

inductive Token where
  | literal (v : Value)
  | binary (op : BinOp)
  | not

def ascii (s : String) : List UInt8 := s.toUTF8.data.toList

def whitespace (b : UInt8) : Prop := b = 32 ∨ b = 9 ∨ b = 13 ∨ b = 10

structure Word where
  bytes : List UInt8
  offset : Nat

/-- Lexemes are maximal runs of non-delimiter bytes with original byte offsets. -/
inductive Words : Nat → List UInt8 → List Word → Prop where
  | done : Words offset [] []
  | space : whitespace b → Words (offset + 1) tail words →
      Words offset (b :: tail) words
  | word : bytes ≠ [] → (∀ b ∈ bytes, ¬ whitespace b) →
      (∀ b, tail.head? = some b → whitespace b) →
      Words (offset + bytes.length) tail words →
      Words offset (bytes ++ tail) (⟨bytes, offset⟩ :: words)

def Recognizes (bytes : List UInt8) : Token → Prop
  | .literal (.number n) => bytes = ascii (toString n.toNat)
  | .literal (.boolean true) => bytes = ascii "true"
  | .literal (.boolean false) => bytes = ascii "false"
  | .binary op => bytes = ascii op.keyword
  | .not => bytes = ascii "not"

abbrev LocatedToken := Token × Nat

def ValidWord (word : Word) : Prop := ∃ token, Recognizes word.bytes token

inductive Lexed : List Word → List LocatedToken → Prop where
  | done : Lexed [] []
  | token : Recognizes word.bytes token → Lexed words tokens →
      Lexed (word :: words) ((token, word.offset) :: tokens)

inductive Expr where
  | literal (v : Value) (offset : Nat)
  | binary (op : BinOp) (offset : Nat) (left right : Expr)
  | not (offset : Nat) (operand : Expr)

/-- A complete program matches the entire prefix token sequence. -/
def Expr.tokens : Expr → List LocatedToken
  | .literal v offset => [(.literal v, offset)]
  | .binary op offset l r => (.binary op, offset) :: (l.tokens ++ r.tokens)
  | .not offset e => (.not, offset) :: e.tokens

/-- A type error names the first failing operator in right-first postorder. -/
def Expr.check : Expr → Except Nat Ty
  | .literal v _ => .ok v.ty
  | .binary op offset l r => do
      let right ← r.check
      let left ← l.check
      let (operand, result) := op.signature
      if left = operand ∧ right = operand then pure result else throw offset
  | .not offset e => do
      let operand ← e.check
      if operand = .bool then pure .bool else throw offset

def Expr.eval : Expr → Option Value
  | .literal v _ => some v
  | .binary op _ l r => do
      let left ← l.eval
      let right ← r.eval
      op.eval left right
  | .not _ e => do
      let .boolean b ← e.eval | none
      some (.boolean (!b))

def BinOp.opcode : BinOp → UInt8
  | .add => 2
  | .sub => 3
  | .eq => 4
  | .lt => 5
  | .and => 6

/-- Operands are emitted right first. Each node contributes one two-byte instruction. -/
def Expr.instructions : Expr → List UInt8
  | .literal v _ => [1, v.byte]
  | .binary op _ l r => r.instructions ++ l.instructions ++ [op.opcode, 0]
  | .not _ e => e.instructions ++ [7, 0]

def Expr.bytecode (e : Expr) : List UInt8 := e.instructions ++ [0, 0]

inductive Diagnostic where
  | codeTooLarge | invalidLexeme | syntax | typeMismatch

inductive Outcome where
  | success (expr : Expr) (ty : Ty)
  | failure (kind : Diagnostic) (offset : Nat)

def maxInt : Nat := 2^63 - 1

def FirstLexError (words : List Word) (offset : Nat) : Prop :=
  ∃ before word tail, words = before ++ word :: tail ∧ offset = word.offset ∧
    (∀ earlier ∈ before, ValidWord earlier) ∧ ¬ ValidWord word

inductive SourceOutcome (source : List UInt8) : Outcome → Prop where
  | lexical : Words 0 source words → FirstLexError words offset →
      SourceOutcome source (.failure .invalidLexeme offset)
  | syntax : Words 0 source words → Lexed words tokens →
      (¬ ∃ expr : Expr, expr.tokens = tokens) → SourceOutcome source (.failure .syntax source.length)
  | typeMismatch {expr : Expr} : Words 0 source words → Lexed words expr.tokens →
      expr.check = .error offset → SourceOutcome source (.failure .typeMismatch offset)
  | codeTooLarge {expr : Expr} : Words 0 source words → Lexed words expr.tokens →
      expr.check = .ok ty → maxInt < 2 * expr.tokens.length + 2 →
      SourceOutcome source (.failure .codeTooLarge source.length)
  | success {expr : Expr} : Words 0 source words → Lexed words expr.tokens →
      expr.check = .ok ty → 2 * expr.tokens.length + 2 ≤ maxInt → SourceOutcome source (.success expr ty)

inductive Status where
  | halt | invalidPC | invalidStack | invalidOpcode

structure State where
  pc : Nat
  stack : Array UInt8

/-- Terminal outcomes preserve the full state. -/
inductive Transition where
  | next (state : State)
  | stop (status : Status)

def binaryOp : UInt8 → Option BinOp
  | 2 => some .add
  | 3 => some .sub
  | 4 => some .eq
  | 5 => some .lt
  | 6 => some .and
  | _ => none

def BinOp.rawResult (op : BinOp) (left right : UInt8) : UInt8 :=
  let operand := if op.signature.1 = .bool then
    fun b : UInt8 => Value.boolean (b != 0)
  else Value.number
  match op.eval (operand left) (operand right) with
  | some value => value.byte
  | none => 0

/-- Every opcode occupies a complete pair, including Halt. -/
def instruction (code : ByteArray) (s : State) : Transition :=
  if s.pc % 2 ≠ 0 ∨ code.size < s.pc + 2 then .stop .invalidPC
  else
    let op := code[s.pc]!
    let stack := s.stack
    if op = 0 then .stop .halt
    else if op = 1 then
      if stack.size = maxInt then .stop .invalidStack
      else .next ⟨s.pc + 2, stack.push code[s.pc + 1]!⟩
    else if op = 7 then
      if stack.size = 0 then .stop .invalidStack
      else .next ⟨s.pc + 2, stack.set! (stack.size - 1) (boolByte (stack.back! == 0))⟩
    else
      match binaryOp op with
      | none => .stop .invalidOpcode
      | some bin =>
        if stack.size < 2 then .stop .invalidStack
        else .next ⟨s.pc + 2, stack.pop.set! (stack.size - 2)
          (bin.rawResult stack.back! stack[stack.size - 2]!)⟩

/-- Execute zero or more continuing instructions, then observe the first halt or fault. -/
inductive Execution (code : ByteArray) : State → Nat → State → Status → Prop where
  | stop : instruction code s = .stop status → Execution code s 1 s status
  | next : instruction code s = .next next → Execution code next steps final status →
      Execution code s (steps + 1) final status

namespace Requirements

def Ty.tag : Spec.Ty → UInt8
  | .u8 => 1
  | .bool => 2

def Diagnostic.tag : Spec.Diagnostic → UInt8
  | .codeTooLarge => 1
  | .invalidLexeme => 2
  | .syntax => 3
  | .typeMismatch => 4

def Status.tag : Spec.Status → UInt8
  | .halt => 1
  | .invalidPC => 2
  | .invalidStack => 3
  | .invalidOpcode => 4

structure Compilation where
  code : ByteArray
  ty : UInt8
  kind : UInt8
  offset : Nat

abbrev Compile := ByteArray → Compilation
abbrev Step := ByteArray → UInt64 → Array UInt8 → Bool → UInt8 × State
abbrev Run := ByteArray → UInt8 × State

def observesCompilation (result : Compilation) : Outcome → Prop
  | .failure kind offset =>
    result.kind = Diagnostic.tag kind ∧ result.offset = offset ∧
    result.code.size = 0 ∧ result.ty = 0
  | .success expr ty =>
    result.kind = 0 ∧ result.offset = 0 ∧
    result.ty = Ty.tag ty ∧ result.code.data.toList = expr.bytecode

/-- Every source has a specified outcome, and compilation meets every such outcome.
    The size bound is the signed Go int range of the generated model's target. -/
def compilationConforms (compile : Compile) : Prop :=
  ∀ source : ByteArray, source.size ≤ maxInt →
    (∃ outcome, SourceOutcome source.data.toList outcome) ∧
    (∀ outcome, SourceOutcome source.data.toList outcome →
      observesCompilation (compile source) outcome)

/-- The alignment flag is supplied by the Go adapter from the PC. -/
def stepConforms (step : Step) : Prop :=
  ∀ code pc stack, code.size ≤ maxInt → stack.size ≤ maxInt →
    let before : State := ⟨pc.toNat, stack⟩
    let (tag, after) := step code pc stack (decide (before.pc % 2 = 0))
    match instruction code before with
    | .next next => tag = 0 ∧ after = next
    | .stop status => tag = Status.tag status ∧ after = before

def executionConforms (run : Run) : Prop :=
  ∀ code : ByteArray, code.size ≤ maxInt →
    let (tag, after) := run code
    ∃ steps final status, steps ≤ code.size / 2 + 1 ∧
      Execution code ⟨0, #[]⟩ steps final status ∧
      tag = Status.tag status ∧ after = final

/-- End-to-end preservation from source bytes through compilation and execution. -/
def preservesSourceMeaning (compile : Compile) (run : Run) : Prop :=
  ∀ (source : ByteArray) expr ty, source.size ≤ maxInt →
    SourceOutcome source.data.toList (.success expr ty) →
    let (tag, final) := run (compile source).code
    ∃ value, expr.eval = some value ∧ value.ty = ty ∧
      tag = Status.tag .halt ∧ final.pc = 2 * expr.tokens.length ∧
      final.stack = #[value.byte]

def all (compile : Compile) (step : Step) (run : Run) : Prop :=
  compilationConforms compile ∧ stepConforms step ∧
    executionConforms run ∧ preservesSourceMeaning compile run

end Requirements
end StackMachineCompiler.Spec
