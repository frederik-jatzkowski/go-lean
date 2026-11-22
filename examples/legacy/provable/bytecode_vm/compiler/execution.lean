import bytecode_vm.compiler.vm_spec

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».Execution

open vm

def Live (state : State) (values : List UInt8) : Prop :=
  state.«field:Depth».toNat = values.length ∧
    ∀ i, i < values.length → state.«field:Stack».getD i 0 = values[i]?.getD 0

private theorem getD_write (stack : Vector UInt8 32) (index i : Nat) (value : UInt8)
    (valid : index < 32) :
    (stack.setIfInBounds index value).getD i 0 =
      if index = i then value else stack.getD i 0 := by
  by_cases hit : index = i
  · subst i
    simp [Vector.getD, valid]
  · simp [Vector.getD, hit]

private theorem replacesSuffix (state : State) (saved suffix : List UInt8) (value depth : UInt8)
    (live : Live state (saved ++ suffix)) (room : saved.length < 32)
    (size : depth.toNat = saved.length + 1) :
    Live (State.mk (state.«field:PC» + 2)
      (state.«field:Stack».setIfInBounds saved.length value) depth) (saved ++ [value]) := by
  refine ⟨by simpa using size, ?_⟩
  intro i valid
  change (state.«field:Stack».setIfInBounds saved.length value).getD i 0 =
    (saved ++ [value])[i]?.getD 0
  rw [getD_write _ _ _ _ room]
  by_cases before : i < saved.length
  · have oldValid : i < (saved ++ suffix).length := by simp; omega
    rw [ite_eq_right (by omega), live.2 i oldValid,
      List.getElem?_append_left before, List.getElem?_append_left before]
  · have atTop : i = saved.length := by simp at valid; omega
    subst i
    simp

private theorem topAt (state : State) (saved rest : List UInt8) (value : UInt8)
    (live : Live state (saved ++ value :: rest)) :
    state.«field:Stack».getD saved.length 0 = value := by
  have valid : saved.length < (saved ++ value :: rest).length := by simp
  simpa [List.getElem?_append_right] using live.2 saved.length valid

def Ready (state : State) : Prop :=
  state.«field:PC».toNat < 64 ∧ state.«field:PC».toNat % 2 = 0

def At (code : Vector UInt8 66) (state : State) (opcode immediate : UInt8) : Prop :=
  code.getD state.«field:PC».toNat 0 = opcode ∧
    code.getD (state.«field:PC».toNat + 1) 0 = immediate

private theorem pcAdvance (state : State) (ready : Ready state) :
    (state.«field:PC» + 2).toNat = state.«field:PC».toNat + 2 := by
  have within := ready.1
  simp [UInt8.toNat_add, Nat.mod_eq_of_lt (show state.«field:PC».toNat + 2 < 256 by omega)]

private theorem guards (state : State) (ready : Ready state) :
    ¬ (state.«field:PC» ≥ 66 ∨ state.«field:PC» % 2 ≠ 0) ∧ state.«field:PC» ≠ 64 := by
  obtain ⟨within, even⟩ := ready
  constructor
  · intro invalid
    rcases invalid with ge | odd
    ·
      have : 66 ≤ state.«field:PC».toNat := UInt8.le_iff_toNat_le.mp ge
      omega
    · exact odd (UInt8.toNat_inj.mp (by simpa [UInt8.toNat_mod] using even))
  · intro same
    rw [same] at within
    contradiction

private theorem depthLE (state : State) (limit : state.«field:Depth».toNat ≤ 32) :
    ¬ 32 < state.«field:Depth» := by
  intro h
  have : 32 < state.«field:Depth».toNat := UInt8.lt_iff_toNat_lt.mp h
  omega

theorem pushes (code : Vector UInt8 66) (state : State) (saved : List UInt8) (value : UInt8)
    (ready : Ready state) (slot : At code state 1 value) (live : Live state saved)
    (room : saved.length < 32) :
    ∃ next, VMModel.step code state = (next, 0) ∧
      next.«field:PC».toNat = state.«field:PC».toNat + 2 ∧ Live next (saved ++ [value]) := by
  rcases guards state ready with ⟨pcOK, notLast⟩
  have depthOK := depthLE state (by rw [live.1]; omega)
  have notFull : state.«field:Depth» ≠ 32 := by
    intro same
    have := live.1
    rw [same] at this
    change 32 = saved.length at this
    omega
  have size : (state.«field:Depth» + 1).toNat = saved.length + 1 := by
    simp [UInt8.toNat_add, live.1, Nat.mod_eq_of_lt (show saved.length + 1 < 256 by omega)]
  refine ⟨State.mk (state.«field:PC» + 2)
    (state.«field:Stack».setIfInBounds saved.length value) (state.«field:Depth» + 1),
    ?_, pcAdvance state ready, ?_⟩
  · simp [VMModel.step, pcOK, notLast, depthOK, notFull, slot.1, slot.2, live.1]
  · apply replacesSuffix state saved [] value _ _ room size
    simpa using live

theorem negates (code : Vector UInt8 66) (state : State) (saved : List UInt8) (value : UInt8)
    (ready : Ready state) (slot : At code state 7 0) (live : Live state (saved ++ [value]))
    (room : (saved ++ [value]).length ≤ 32) :
    ∃ next, VMModel.step code state = (next, 0) ∧
      next.«field:PC».toNat = state.«field:PC».toNat + 2 ∧
      Live next (saved ++ [VMModel.boolByte (decide (value = 0))]) := by
  rcases guards state ready with ⟨pcOK, notLast⟩
  have depthOK := depthLE state (by rw [live.1]; exact room)
  have size : state.«field:Depth».toNat = saved.length + 1 := by simpa using live.1
  have notEmpty : state.«field:Depth» ≠ 0 := by
    intro same
    rw [same] at size
    change 0 = saved.length + 1 at size
    omega
  have top := topAt state saved [] value live
  let result := VMModel.boolByte (decide (value = 0))
  refine ⟨State.mk (state.«field:PC» + 2)
    (state.«field:Stack».setIfInBounds saved.length result) state.«field:Depth»,
    ?_, pcAdvance state ready, replacesSuffix state saved [value] result _ live (by simp at room; omega) size⟩
  · simp [VMModel.step, pcOK, notLast, depthOK, notEmpty, slot.1, size, top, result]

theorem combines (code : Vector UInt8 66) (state : State) (saved : List UInt8)
    (opcode left right : UInt8) (opLo : 2 ≤ opcode) (opHi : opcode ≤ 6)
    (ready : Ready state) (slot : At code state opcode 0) (live : Live state (saved ++ [right, left]))
    (room : (saved ++ [right, left]).length ≤ 32) :
    ∃ next, VMModel.step code state = (next, 0) ∧
      next.«field:PC».toNat = state.«field:PC».toNat + 2 ∧
      Live next (saved ++ [VMModel.binary opcode left right]) := by
  rcases guards state ready with ⟨pcOK, notLast⟩
  have depthOK := depthLE state (by rw [live.1]; exact room)
  have lo : 2 ≤ opcode.toNat := UInt8.le_iff_toNat_le.mp opLo
  have hi : opcode.toNat ≤ 6 := UInt8.le_iff_toNat_le.mp opHi
  have notZero : opcode ≠ 0 := by intro h; rw [h] at lo; contradiction
  have notOne : opcode ≠ 1 := by intro h; rw [h] at lo; contradiction
  have notSeven : opcode ≠ 7 := by intro h; rw [h] at hi; contradiction
  have opcodeOK : ¬ 7 < opcode := by
    intro h
    have : 7 < opcode.toNat := UInt8.lt_iff_toNat_lt.mp h
    omega
  have size : state.«field:Depth».toNat = saved.length + 2 := by simpa using live.1
  have enough : ¬ state.«field:Depth» < 2 := by
    intro h
    have : state.«field:Depth».toNat < 2 := UInt8.lt_iff_toNat_lt.mp h
    omega
  have nextSize : (state.«field:Depth» - 1).toNat = saved.length + 1 := by
    have enoughOne : (1 : UInt8) ≤ state.«field:Depth» :=
      UInt8.le_iff_toNat_le.mpr (show 1 ≤ state.«field:Depth».toNat by omega)
    rw [UInt8.toNat_sub_of_le _ _ enoughOne, size]
    simp
  have below := topAt state saved [left] right live
  have top : state.«field:Stack».getD (saved.length + 1) 0 = left := by
    have expanded : Live state ((saved ++ [right]) ++ [left]) := by simpa [List.append_assoc] using live
    simpa using topAt state (saved ++ [right]) [] left expanded
  let result := VMModel.binary opcode left right
  refine ⟨State.mk (state.«field:PC» + 2)
    (state.«field:Stack».setIfInBounds saved.length result) (state.«field:Depth» - 1),
    ?_, pcAdvance state ready, replacesSuffix state saved [right, left] result _ live (by simp at room; omega) nextSize⟩
  · simp [VMModel.step, pcOK, notLast, depthOK, slot.1, notZero, notOne, notSeven,
      opcodeOK, enough, size, below, top, result]

theorem halts (code : Vector UInt8 66) (state : State)
    (pcBound : state.«field:PC».toNat < 66) (aligned : state.«field:PC».toNat % 2 = 0)
    (depthBound : state.«field:Depth».toNat ≤ 32) (slot : code.getD state.«field:PC».toNat 0 = 0) :
    VMModel.step code state = (state, 1) := by
  have pcOK : ¬ (state.«field:PC» ≥ 66 ∨ state.«field:PC» % 2 ≠ 0) := by
    intro invalid
    rcases invalid with ge | odd
    ·
      have : 66 ≤ state.«field:PC».toNat := UInt8.le_iff_toNat_le.mp ge
      omega
    · exact odd (UInt8.toNat_inj.mp (by simpa [UInt8.toNat_mod] using aligned))
  simp [VMModel.step, pcOK, depthLE state depthBound, slot]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».Execution
