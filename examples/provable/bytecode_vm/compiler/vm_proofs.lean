import bytecode_vm.compiler.vm_laws

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».vm.Proofs

private theorem binaryMatches (opcode left right : UInt8) :
    binaryResult opcode left right = VMModel.binary opcode left right := by
  by_cases add : opcode = 2
  · simp [binaryResult, VMModel.binary, add]
  by_cases sub : opcode = 3
  · simp [binaryResult, VMModel.binary, sub]
  by_cases eq : opcode = 4
  · simp [binaryResult, VMModel.binary, eq, truthByte, VMModel.boolByte]
  by_cases lt : opcode = 5
  · simp [binaryResult, VMModel.binary, lt, truthByte, VMModel.boolByte]
  by_cases leftZero : left = 0 <;>
    simp [binaryResult, VMModel.binary, add, sub, eq, lt, truthByte, VMModel.boolByte, leftZero]

private theorem fetched {n : Nat} (bytes : Vector UInt8 n) {i : Nat} (inside : i < n) :
    bytes.toArray[i]? = some (bytes.getD i 0) := by
  simp [Vector.getD, inside]

theorem stepMatchesSpec : Laws.stepMatchesSpec := by
  intro code state
  rcases state with ⟨pc, stack, depth⟩
  by_cases outside : 66 ≤ pc
  · simp [Step, VMModel.step, outside]
  by_cases odd : pc % 2 ≠ 0
  · simp [Step, VMModel.step, outside, odd]
  have evenWord : pc % 2 = 0 := Decidable.byContradiction odd
  by_cases tooDeep : 32 < depth
  · simp [Step, VMModel.step, outside, evenWord, tooDeep]
  have pcBound : pc.toNat < 66 :=
    Nat.lt_of_not_ge (fun h => outside (UInt8.le_iff_toNat_le.mpr h))
  have depthBound : depth.toNat ≤ 32 :=
    Nat.le_of_not_gt (fun h => tooDeep (UInt8.lt_iff_toNat_lt.mpr h))
  have readOpcode := fetched code pcBound
  by_cases unknown : 7 < code.getD pc.toNat 0
  · simp [Step, VMModel.step, outside, evenWord, tooDeep, readOpcode, unknown]
  by_cases halt : code.getD pc.toNat 0 = 0
  · simp [Step, VMModel.step, outside, evenWord, tooDeep, readOpcode, halt]
  by_cases last : pc = 64
  · subst pc
    have lastValue : code[64] = code.getD 64 0 := by
      simpa using fetched code (show 64 < 66 by decide)
    have lastKnown : ¬7 < code.getD 64 0 := unknown
    have lastRunning : code.getD 64 0 ≠ 0 := halt
    simp [Step, VMModel.step, tooDeep, lastValue, lastKnown, lastRunning]
  by_cases push : code.getD pc.toNat 0 = 1
  · by_cases full : depth = 32
    · simp [Step, VMModel.step, outside, evenWord, readOpcode, last, push, full]
    have noFull : depth.toNat ≠ 32 := fun h => full (UInt8.toNat_inj.mp h)
    have slot : depth.toNat < 32 := by omega
    have immediate : (pc + 1).toNat = pc.toNat + 1 := by
      simp only [UInt8.toNat_add]
      change (pc.toNat + 1) % 256 = pc.toNat + 1
      omega
    have aligned : pc.toNat % 2 = 0 := by simpa using congrArg UInt8.toNat evenWord
    have dataBound : pc.toNat + 1 < 66 := by omega
    have readImmediate := fetched code dataBound
    have readSlot := fetched stack slot
    simp [-UInt8.toNat_add, Step, VMModel.step, outside, evenWord, tooDeep, readOpcode,
      last, push, full, immediate, readImmediate, readSlot]
  by_cases negate : code.getD pc.toNat 0 = 7
  · by_cases empty : depth = 0
    · simp [Step, VMModel.step, outside, evenWord, readOpcode, last, negate, empty]
    have positive : 0 < depth.toNat := by
      have nonzero : depth.toNat ≠ 0 := fun h => empty (UInt8.toNat_inj.mp h)
      omega
    have top : (depth - 1).toNat = depth.toNat - 1 :=
      UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr positive)
    have topBound : depth.toNat - 1 < 32 := by omega
    have readTop := fetched stack topBound
    simp [Step, VMModel.step, outside, evenWord, tooDeep, readOpcode, last, negate,
      empty, top, readTop, truthByte, VMModel.boolByte]
  by_cases tooShallow : depth < 2
  · simp [Step, VMModel.step, outside, evenWord, tooDeep, readOpcode, unknown, halt, last, push, negate, tooShallow]
  have enough : 2 ≤ depth.toNat :=
    Nat.le_of_not_gt (fun h => tooShallow (UInt8.lt_iff_toNat_lt.mpr h))
  have top : (depth - 1).toNat = depth.toNat - 1 :=
    UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr (show 1 ≤ depth.toNat by omega))
  have below : (depth - 2).toNat = depth.toNat - 2 :=
    UInt8.toNat_sub_of_le _ _ (UInt8.le_iff_toNat_le.mpr enough)
  have topBound : depth.toNat - 1 < 32 := by omega
  have belowBound : depth.toNat - 2 < 32 := by omega
  have readTop := fetched stack topBound
  have readBelow := fetched stack belowBound
  simp [Step, VMModel.step, outside, evenWord, tooDeep, readOpcode, unknown, halt, last, push, negate,
    tooShallow, top, below, readTop, readBelow, binaryMatches]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/bytecode_vm/compiler».vm.Proofs
