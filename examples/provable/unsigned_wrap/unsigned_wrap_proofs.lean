import unsigned_wrap.unsigned_wrap_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/unsigned_wrap».unsigned_wrap.Proofs

theorem increment8Wraps : Laws.increment8Wraps := by
  unfold Laws.increment8Wraps
  decide

theorem increment16Wraps : Laws.increment16Wraps := by
  unfold Laws.increment16Wraps
  decide

theorem increment32Wraps : Laws.increment32Wraps := by
  unfold Laws.increment32Wraps
  decide

theorem increment64Wraps : Laws.increment64Wraps := by
  unfold Laws.increment64Wraps
  decide

theorem zeroDivisorPanics : Laws.zeroDivisorPanics := by
  intro value
  simp [Quotient64]

theorem quotientUsesUnsignedMagnitude : Laws.quotientUsesUnsignedMagnitude := by
  unfold Laws.quotientUsesUnsignedMagnitude
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/unsigned_wrap».unsigned_wrap.Proofs
