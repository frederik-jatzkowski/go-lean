namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Spec

inductive BinaryOp where
  | add | sub | eq | lt | and
  deriving DecidableEq

inductive Expr where
  | number (value : UInt8) (start : Nat)
  | boolean (value : Bool) (start : Nat)
  | unary (start : Nat) (operand : Expr)
  | binary (op : BinaryOp) (start : Nat) (left right : Expr)
  deriving DecidableEq

inductive Value where
  | u8 (value : UInt8)
  | boolean (value : Bool)
  deriving DecidableEq

def Value.type : Value → UInt8
  | .u8 _ => 1
  | .boolean _ => 2

def Value.encode : Value → UInt8
  | .u8 n => n
  | .boolean b => if b then 1 else 0

theorem Value.boolEncoding (value : Value) (boolean : value.type = 2) :
    value.encode = 0 ∨ value.encode = 1 := by
  cases value with
  | u8 n => simp [Value.type] at boolean
  | boolean b => cases b <;> decide

def BinaryOp.eval : BinaryOp → Value → Value → Option Value
  | .add, .u8 x, .u8 y => some (.u8 (x + y))
  | .sub, .u8 x, .u8 y => some (.u8 (x - y))
  | .eq, .u8 x, .u8 y => some (.boolean (x == y))
  | .lt, .u8 x, .u8 y => some (.boolean (decide (x < y)))
  | .and, .boolean x, .boolean y => some (.boolean (x && y))
  | _, _, _ => none

def Expr.eval : Expr → Option Value
  | .number n _ => some (.u8 n)
  | .boolean b _ => some (.boolean b)
  | .unary _ operand => do
    let .boolean value ← operand.eval | none
    pure (.boolean (!value))
  | .binary op _ left right => do
    let y ← right.eval
    let x ← left.eval
    op.eval x y

def BinaryOp.signature : BinaryOp → UInt8 × UInt8
  | .add | .sub => (1, 1)
  | .eq | .lt => (1, 2)
  | .and => (2, 2)

/-- Report the first rejected operator and record all inferred types in evaluation order. -/
def Expr.typeCheck : Expr → Except Nat (List UInt8 × UInt8)
  | .number .. => .ok ([1], 1)
  | .boolean .. => .ok ([2], 2)
  | .unary start operand => do
    let (operandTypes, operandType) ← operand.typeCheck
    if operandType = 2 then pure (operandTypes ++ [2], 2) else .error start
  | .binary op start left right => do
    let (rightTypes, rightType) ← right.typeCheck
    let (leftTypes, leftType) ← left.typeCheck
    let (input, output) := op.signature
    if leftType = input ∧ rightType = input then
      pure (rightTypes ++ leftTypes ++ [output], output)
    else .error start

private theorem binaryEvalTyped (op : BinaryOp) (left right : Value) :
    (op.eval left right).map Value.type =
      if left.type = op.signature.1 ∧ right.type = op.signature.1
      then some op.signature.2 else none := by
  cases op <;> cases left <;> cases right <;> simp [BinaryOp.eval, BinaryOp.signature, Value.type]

theorem Expr.evalType (expr : Expr) : expr.eval.map Value.type =
    match expr.typeCheck with
    | .ok (_, ty) => some ty
    | .error _ => none := by
  induction expr with
  | number n start => rfl
  | boolean b start => rfl
  | unary start operand ih =>
    cases computed : operand.eval with
    | none =>
      cases checked : operand.typeCheck with
      | ok result => simp [computed, checked] at ih
      | error e => simp [Expr.eval, Expr.typeCheck, computed, checked, bind, Except.bind, pure]
    | some value =>
      cases checked : operand.typeCheck with
      | error e => simp [computed, checked] at ih
      | ok result =>
        rcases result with ⟨entries, ty⟩
        simp only [computed, checked, Option.map_some, Option.some.injEq] at ih
        subst ty
        cases value <;>
          simp [Expr.eval, Expr.typeCheck, Value.type, computed, checked, bind, Except.bind, pure, Except.pure]
  | binary op start left right leftIH rightIH =>
    cases r : right.eval <;> cases rt : right.typeCheck <;>
      simp [r, rt] at rightIH
    · simp [Expr.eval, Expr.typeCheck, r, rt, bind, Except.bind]
    · rename_i rightValue rightResult
      rcases rightResult with ⟨rightTypes, rightType⟩
      change rightValue.type = rightType at rightIH
      subst rightType
      cases l : left.eval <;> cases lt : left.typeCheck <;>
        simp [l, lt] at leftIH
      · simp [Expr.eval, Expr.typeCheck, r, rt, l, lt, bind, Except.bind]
      · rename_i leftValue leftResult
        rcases leftResult with ⟨leftTypes, leftType⟩
        change leftValue.type = leftType at leftIH
        subst leftType
        by_cases operands : leftValue.type = op.signature.1 ∧ rightValue.type = op.signature.1 <;>
          simp [Expr.eval, Expr.typeCheck, r, rt, l, lt, bind, Except.bind, pure, Except.pure,
            binaryEvalTyped, operands]

inductive Instruction where
  | halt
  | push (value : UInt8)
  | add | sub | eq | lt | and | not
  deriving DecidableEq

def Instruction.encode : Instruction → List UInt8
  | .halt => [0, 0]
  | .push value => [1, value]
  | .add => [2, 0]
  | .sub => [3, 0]
  | .eq => [4, 0]
  | .lt => [5, 0]
  | .and => [6, 0]
  | .not => [7, 0]

def BinaryOp.instruction : BinaryOp → Instruction
  | .add => .add
  | .sub => .sub
  | .eq => .eq
  | .lt => .lt
  | .and => .and

def Expr.code : Expr → List Instruction
  | .number n _ => [.push n]
  | .boolean b _ => [.push (Value.boolean b).encode]
  | .unary _ operand => operand.code ++ [.not]
  | .binary op _ left right => right.code ++ left.code ++ [op.instruction]

def Expr.nodeCount : Expr → Nat
  | .number .. | .boolean .. => 1
  | .unary _ operand => operand.nodeCount + 1
  | .binary _ _ left right => right.nodeCount + left.nodeCount + 1

theorem Expr.codeLength (expr : Expr) : expr.code.length = expr.nodeCount := by
  induction expr <;> simp_all [Expr.code, Expr.nodeCount, Nat.add_assoc]

theorem Expr.typeTableShape (expr : Expr) (ok : expr.typeCheck = .ok (entries, ty)) :
    entries.length = expr.nodeCount ∧ entries[entries.length-1]? = some ty := by
  induction expr generalizing entries ty with
  | number | boolean =>
    simp [Expr.typeCheck] at ok
    obtain ⟨rfl, rfl⟩ := ok
    exact ⟨rfl, rfl⟩
  | unary start operand ih =>
    cases child : operand.typeCheck with
    | error offset => simp [Expr.typeCheck, child, bind, Except.bind] at ok
    | ok result =>
      rcases result with ⟨childTypes, childType⟩
      by_cases accepted : childType = 2
      · have shape := ih child
        simp [Expr.typeCheck, child, bind, Except.bind, pure, Except.pure, accepted] at ok
        obtain ⟨rfl, rfl⟩ := ok
        simp [Expr.nodeCount, shape.1]
      · simp [Expr.typeCheck, child, bind, Except.bind, accepted] at ok
  | binary op start left right ihLeft ihRight =>
    cases r : right.typeCheck with
    | error offset => simp [Expr.typeCheck, r, bind, Except.bind] at ok
    | ok rightResult =>
      rcases rightResult with ⟨rightTypes, rightType⟩
      cases l : left.typeCheck with
      | error offset => simp [Expr.typeCheck, r, l, bind, Except.bind] at ok
      | ok leftResult =>
        rcases leftResult with ⟨leftTypes, leftType⟩
        by_cases accepted : leftType = op.signature.1 ∧ rightType = op.signature.1
        · have lshape := ihLeft l
          have rshape := ihRight r
          simp [Expr.typeCheck, r, l, bind, Except.bind, pure, Except.pure, accepted] at ok
          obtain ⟨rfl, rfl⟩ := ok
          simp [Expr.nodeCount, lshape.1, rshape.1, Nat.add_assoc]
        · simp [Expr.typeCheck, r, l, bind, Except.bind, accepted] at ok

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».compiler.Spec
