import bytecode_vm.compiler.compiler_spec
import bytecode_vm.compiler.execution
import bytecode_vm.compiler.vm_verify
import Lean.Util.CollectAxioms

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».Execution

open vm compiler.Spec

def Covers (code : Vector UInt8 66) (pc : Nat) (instructions : List Instruction) : Prop :=
  ∀ i, i < (instructions.flatMap Instruction.encode).length →
    code.getD (pc + i) 0 = (instructions.flatMap Instruction.encode)[i]?.getD 0

theorem byteLength (instructions : List Instruction) :
    (instructions.flatMap Instruction.encode).length = 2 * instructions.length := by
  induction instructions with
  | nil => rfl
  | cons instruction tail ih =>
    cases instruction <;> simp [Instruction.encode, ih] <;> omega

theorem coversPacked (instructions : List Instruction) (fits : instructions.length ≤ 33) :
    Covers (Vector.ofFn (fun i : Fin 66 =>
      (instructions.flatMap Instruction.encode)[i.val]?.getD 0)) 0 instructions := by
  intro i bound
  have within : i < 66 := by rw [byteLength] at bound; omega
  simp [Vector.getD, within]

theorem coversLeft (code : Vector UInt8 66) (pc : Nat) (left right : List Instruction)
    (cover : Covers code pc (left ++ right)) : Covers code pc left := by
  intro i bound
  have indexed := cover i (by rw [List.flatMap_append, List.length_append]; omega)
  simpa only [List.flatMap_append, List.getElem?_append_left bound] using indexed

theorem coversRight (code : Vector UInt8 66) (pc : Nat) (left right : List Instruction)
    (cover : Covers code pc (left ++ right)) :
    Covers code (pc + 2 * left.length) right := by
  intro i bound
  have indexed := cover ((left.flatMap Instruction.encode).length + i)
    (by rw [List.flatMap_append, List.length_append]; omega)
  rw [List.flatMap_append, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left] at indexed
  simpa only [Nat.add_assoc, byteLength] using indexed

def opcodeOf (instruction : Instruction) : UInt8 := instruction.encode[0]?.getD 0

def immediateOf (instruction : Instruction) : UInt8 := instruction.encode[1]?.getD 0

theorem coversAt (code : Vector UInt8 66) (state : State) (instruction : Instruction)
    (cover : Covers code state.«field:PC».toNat [instruction]) :
    At code state (opcodeOf instruction) (immediateOf instruction) := by
  constructor
  · simpa [opcodeOf] using cover 0 (by simp only [byteLength, List.length_singleton]; decide)
  · simpa [immediateOf] using cover 1 (by simp only [byteLength, List.length_singleton]; decide)

/-- Exactly this many normal instructions execute, with an aligned PC and bounded stack
    at each step. A terminal status cannot occur inside this relation. -/
inductive Continues (code : Vector UInt8 66) : State → Nat → State → Prop where
  | empty (state) : Continues code state 0 state
  | next {start middle final count} (ready : Ready start)
      (depthBound : start.«field:Depth».toNat ≤ 32)
      (step : Step code start = some (middle, 0))
      (tail : Continues code middle count final) :
      Continues code start (count + 1) final

theorem Continues.append {code : Vector UInt8 66} {start middle final : State} {n m : Nat}
    (left : Continues code start n middle) (right : Continues code middle m final) :
    Continues code start (n + m) final := by
  induction left with
  | empty => simpa using right
  | @next start middle final count ready bound step _ ih =>
    rw [show count + 1 + m = (count + m) + 1 by omega]
    exact .next ready bound step (ih right)

private theorem oneStep {code : Vector UInt8 66} {start final : State} (ready : Ready start)
    (depthBound : start.«field:Depth».toNat ≤ 32) (step : VMModel.step code start = (final, 0)) :
    Continues code start 1 final :=
  .next ready depthBound (by rw [Checked.stepMatchesSpec, step]) (.empty final)

private theorem binaryEncoding (op : BinaryOp) (left right result : Value)
    (evaluated : op.eval left right = some result) :
    VMModel.binary (opcodeOf op.instruction) left.encode right.encode = result.encode := by
  cases op <;> cases left <;> cases right <;>
    simp [BinaryOp.eval] at evaluated
  all_goals subst result
  all_goals simp [BinaryOp.instruction, opcodeOf, Instruction.encode, Value.encode,
    VMModel.binary, VMModel.boolByte]
  · rename_i x y
    change (if decide (x = y) = true then 1 else 0 : UInt8) = if x = y then 1 else 0
    simp only [decide_eq_true_eq]
  · rename_i x y
    change (if decide (x < y) = true then 1 else 0 : UInt8) = if x < y then 1 else 0
    simp only [decide_eq_true_eq]

private theorem binaryOpcode (op : BinaryOp) :
    2 ≤ opcodeOf op.instruction ∧ opcodeOf op.instruction ≤ 6 := by
  cases op <;> decide

private theorem hasNode (expr : Expr) : 1 ≤ expr.nodeCount := by
  cases expr <;> simp [Expr.nodeCount]

theorem subtree (code : Vector UInt8 66) (expr : Expr) (value : Value) (start : State)
    (saved : List UInt8) (eval : expr.eval = some value)
    (cover : Covers code start.«field:PC».toNat expr.code)
    (aligned : start.«field:PC».toNat % 2 = 0)
    (pcRoom : start.«field:PC».toNat + 2 * expr.nodeCount ≤ 64)
    (live : Live start saved) (stackRoom : saved.length + expr.nodeCount ≤ 32) :
    ∃ final, Continues code start expr.nodeCount final ∧
      final.«field:PC».toNat = start.«field:PC».toNat + 2 * expr.nodeCount ∧
      Live final (saved ++ [value.encode]) := by
  induction expr generalizing value start saved with
  | number n position =>
    simp [Expr.eval] at eval
    subst value
    simp only [Expr.nodeCount] at pcRoom stackRoom ⊢
    have ready : Ready start := ⟨by omega, aligned⟩
    have slot := coversAt code start (.push n) cover
    obtain ⟨final, stepped, advanced, loaded⟩ :=
      pushes code start saved n ready slot live (by omega)
    exact ⟨final, oneStep ready (by rw [live.1]; omega) stepped, advanced, loaded⟩
  | boolean b position =>
    simp [Expr.eval] at eval
    subst value
    simp only [Expr.nodeCount] at pcRoom stackRoom ⊢
    have ready : Ready start := ⟨by omega, aligned⟩
    have slot := coversAt code start (.push (Value.boolean b).encode) cover
    obtain ⟨final, stepped, advanced, loaded⟩ :=
      pushes code start saved (Value.boolean b).encode ready slot live (by omega)
    exact ⟨final, oneStep ready (by rw [live.1]; omega) stepped, advanced, loaded⟩
  | unary position operand ih =>
    cases operandEval : operand.eval with
    | none => simp [Expr.eval, operandEval] at eval
    | some operandValue =>
      cases operandValue with
      | u8 n => simp [Expr.eval, operandEval] at eval
      | boolean b =>
        simp [Expr.eval, operandEval] at eval
        subst value
        simp only [Expr.nodeCount] at pcRoom stackRoom ⊢
        have operandCover := coversLeft code start.«field:PC».toNat operand.code [.not] cover
        obtain ⟨middle, ran, advanced, loaded⟩ :=
          ih (.boolean b) start saved operandEval operandCover aligned (by omega) live (by omega)
        have middleReady : Ready middle := ⟨by omega, by omega⟩
        have opCover := coversRight code start.«field:PC».toNat operand.code [.not] cover
        rw [operand.codeLength, ← advanced] at opCover
        have slot := coversAt code middle .not opCover
        obtain ⟨final, stepped, finished, loadedFinal⟩ :=
          negates code middle saved _ middleReady slot loaded (by simp; omega)
        have after : Continues code middle 1 final :=
          oneStep middleReady (by rw [loaded.1]; simp; omega) stepped
        refine ⟨final, ran.append after, by omega, ?_⟩
        cases b <;> exact loadedFinal
  | binary op position left right leftIH rightIH =>
    cases rightEval : right.eval with
    | none => simp [Expr.eval, rightEval] at eval
    | some rightValue =>
      cases leftEval : left.eval with
      | none => simp [Expr.eval, rightEval, leftEval] at eval
      | some leftValue =>
        have resultEval : op.eval leftValue rightValue = some value := by
          simpa [Expr.eval, rightEval, leftEval] using eval
        simp only [Expr.nodeCount] at pcRoom stackRoom ⊢
        have whole : Covers code start.«field:PC».toNat
            (right.code ++ (left.code ++ [op.instruction])) := by
          simpa only [Expr.code, List.append_assoc] using cover
        have rightCover := coversLeft code start.«field:PC».toNat right.code
          (left.code ++ [op.instruction]) whole
        obtain ⟨afterRight, rightRan, rightPC, rightLive⟩ :=
          rightIH rightValue start saved rightEval rightCover aligned (by omega) live (by omega)
        have remaining := coversRight code start.«field:PC».toNat right.code
          (left.code ++ [op.instruction]) whole
        rw [right.codeLength, ← rightPC] at remaining
        have leftCover := coversLeft code afterRight.«field:PC».toNat left.code [op.instruction] remaining
        obtain ⟨afterLeft, leftRan, leftPC, leftLive⟩ :=
          leftIH leftValue afterRight (saved ++ [rightValue.encode]) leftEval leftCover
            (by omega) (by omega) rightLive (by simp; omega)
        have binaryCover := coversRight code afterRight.«field:PC».toNat left.code
          [op.instruction] remaining
        rw [left.codeLength, ← leftPC] at binaryCover
        have pair : Live afterLeft (saved ++ [rightValue.encode, leftValue.encode]) := by
          simpa [List.append_assoc] using leftLive
        have ready : Ready afterLeft := ⟨by omega, by omega⟩
        have slot : At code afterLeft (opcodeOf op.instruction) 0 := by
          have atOp := coversAt code afterLeft op.instruction binaryCover
          cases op <;> exact atOp
        have pairRoom : (saved ++ [rightValue.encode, leftValue.encode]).length ≤ 32 := by
          have := hasNode left
          simp
          omega
        obtain ⟨final, stepped, advanced, result⟩ :=
          combines code afterLeft saved (opcodeOf op.instruction) leftValue.encode rightValue.encode
            (binaryOpcode op).1 (binaryOpcode op).2 ready slot pair pairRoom
        have last : Continues code afterLeft 1 final :=
          oneStep ready (by rw [pair.1]; exact pairRoom) stepped
        rw [binaryEncoding op leftValue rightValue value resultEval] at result
        exact ⟨final, (rightRan.append leftRan).append last, by omega, result⟩

theorem compiledHalts (code : Vector UInt8 66) (start : State) (expr : Expr) (value : Value)
    (eval : expr.eval = some value) (cover : Covers code 0 (expr.code ++ [.halt]))
    (fits : expr.nodeCount ≤ 32) (pcZero : start.«field:PC».toNat = 0) (empty : Live start []) :
    ∃ final, Continues code start expr.nodeCount final ∧
      final.«field:PC».toNat = 2 * expr.nodeCount ∧
      Step code final = some (final, 1) ∧ Live final [value.encode] := by
  have body := coversLeft code 0 expr.code [.halt] cover
  rw [← pcZero] at body
  obtain ⟨final, ran, pc, result⟩ :=
    subtree code expr value start [] eval body (by rw [pcZero])
      (by omega) empty (by simpa using fits)
  have finalPC : final.«field:PC».toNat = 2 * expr.nodeCount := by omega
  have halt := coversRight code 0 expr.code [.halt] cover
  rw [expr.codeLength, Nat.zero_add, ← finalPC] at halt
  have haltSlot := (coversAt code final .halt halt).1
  have terminal := halts code final (by omega) (by omega) (by simp [result.1]) haltSlot
  exact ⟨final, ran, finalPC, by rw [Checked.stepMatchesSpec, terminal], result⟩

run_cmd
  for theoremName in [``coversPacked, ``compiledHalts] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless [`propext, `Quot.sound, `Classical.choice].contains axiomName do
        throwError "Compiler execution proof {theoremName} depends on unapproved axiom {axiomName}"

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».Execution
