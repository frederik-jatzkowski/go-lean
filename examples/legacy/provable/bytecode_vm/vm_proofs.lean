import bytecode_vm.vm_gen
import Lean.Util.CollectAxioms

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm».vm.Proofs

/-- The instruction contract gives the entire state and status for each fetched byte.
    A missing byte or an unavailable fallthrough address is an invalid PC. -/
def instructionSpec (program : Vector UInt8 8) (state : State) : State × UInt8 :=
  let pc := state.«field:PC»
  let accumulator := state.«field:Accumulator»
  let fallthroughState (value : UInt8) : State × UInt8 :=
    if pc = 7 then (state, 2) else (⟨pc + 1, value⟩, 0)
  match program.toArray[pc.toNat]? with
  | none => (state, 2)
  | some opcode =>
    if opcode = 0 then (state, 1)
    else if opcode = 1 then fallthroughState (accumulator + 1)
    else if opcode = 2 then (⟨0, accumulator⟩, 0)
    else if opcode = 3 then fallthroughState (accumulator - 1)
    else (state, 3)

theorem stepMatchesSpec (program : Vector UInt8 8) (state : State) :
    Step program state = some (instructionSpec program state) := by
  rcases state with ⟨pc, accumulator⟩
  by_cases outside : 8 ≤ pc
  · have missing : program.toArray[pc.toNat]? = none := by
      apply getElem?_neg
      simpa [program.size_toArray] using Nat.not_lt.mpr (UInt8.le_iff_toNat_le.mp outside)
    simp [Step, instructionSpec, outside, missing]
  · have within : pc.toNat < program.toArray.size := by
      rw [program.size_toArray]
      apply Nat.lt_of_not_ge
      exact fun h => outside (UInt8.le_iff_toNat_le.mpr h)
    have fetched := getElem?_pos program.toArray pc.toNat within
    by_cases halt : program.toArray[pc.toNat] = 0
    · simp [Step, instructionSpec, outside, fetched, halt]
    by_cases jump : program.toArray[pc.toNat] = 2
    · simp [Step, instructionSpec, outside, fetched, jump]
    by_cases inc : program.toArray[pc.toNat] = 1
    · by_cases last : pc = 7 <;> simp_all [Step, instructionSpec]
    by_cases dec : program.toArray[pc.toNat] = 3
    · by_cases last : pc = 7 <;> simp_all [Step, instructionSpec]
    · simp [Step, instructionSpec, outside, fetched]
      simp_all

theorem stepReturnsNormally : Laws.stepReturnsNormally := by
  intro program state
  exact ⟨instructionSpec program state, stepMatchesSpec program state⟩

private theorem specKeepsPCInBounds (program : Vector UInt8 8) (state : State)
    (within : state.«field:PC» < 8) :
    (instructionSpec program state).1.«field:PC» < 8 := by
  rcases state with ⟨pc, accumulator⟩
  have nextWithin (beforeLast : pc ≠ 7) : pc + 1 < 8 := by
    change pc < 8 at within
    have bound : pc.toNat < 8 := UInt8.lt_iff_toNat_lt.mp within
    have notLast : pc.toNat ≠ 7 := by
      intro last
      apply beforeLast
      exact UInt8.toNat_inj.mp last
    apply UInt8.lt_iff_toNat_lt.mpr
    simp [UInt8.toNat_add]
    omega
  simp only [instructionSpec]
  split
  · exact within
  · split <;> try split <;> try split <;> try split <;> try split
    all_goals first | exact within | exact (show (0 : UInt8) < 8 by decide) | exact nextWithin (by assumption)

/-- Any continuing Go step has a valid next PC. In fact, a valid PC stays
    valid even when the instruction halts or reports an error. -/
theorem stepKeepsPCInBounds (program : Vector UInt8 8) (state next : State) (status : UInt8)
    (within : state.«field:PC» < 8) (step : Step program state = some (next, status)) :
    next.«field:PC» < 8 := by
  rw [stepMatchesSpec] at step
  have same := congrArg Prod.fst (Option.some.inj step)
  change (instructionSpec program state).1 = next at same
  rw [← same]
  exact specKeepsPCInBounds program state within

/-- Execute up to the given number of steps, retaining the first terminal result. -/
def runPrefix (step : State → Option (State × UInt8)) :
    Nat → Option (State × UInt8)
  | 0 => some (⟨0, 0⟩, 0)
  | n + 1 => do
    let (state, status) ← runPrefix step n
    if status = 0 then step state else some (state, status)

theorem everyPrefixMatchesSpec (program : Vector UInt8 8) (steps : Nat) :
    runPrefix (Step program) steps = runPrefix (fun state => some (instructionSpec program state)) steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [runPrefix, ih]
    cases runPrefix (fun state => some (instructionSpec program state)) steps with
    | none => rfl
    | some result =>
      rcases result with ⟨state, status⟩
      simp [stepMatchesSpec]

theorem everyPrefixIsSafe (program : Vector UInt8 8) (steps : Nat) :
    ∃ state status, runPrefix (Step program) steps = some (state, status) ∧ state.«field:PC» < 8 := by
  induction steps with
  | zero => exact ⟨⟨0, 0⟩, 0, rfl, by decide⟩
  | succ steps ih =>
    obtain ⟨state, status, previous, within⟩ := ih
    rcases result : instructionSpec program state with ⟨next, outcome⟩
    have step : Step program state = some (next, outcome) := by rw [stepMatchesSpec, result]
    by_cases continuing : status = 0
    · exact ⟨next, outcome, by simp [runPrefix, previous, continuing, step],
        stepKeepsPCInBounds program state next outcome within step⟩
    · exact ⟨state, status, by simp [runPrefix, previous, continuing], within⟩

run_cmd
  for theoremName in [``everyPrefixMatchesSpec, ``everyPrefixIsSafe] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless [`propext, `Quot.sound, `Classical.choice].contains axiomName do
        throwError "VM proof {theoremName} depends on unapproved axiom {axiomName}"

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm».vm.Proofs
