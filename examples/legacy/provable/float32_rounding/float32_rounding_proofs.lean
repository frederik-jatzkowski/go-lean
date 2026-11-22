import float32_rounding.float32_rounding_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float32_rounding».float32_rounding.Proofs

theorem addUnitAtPrecisionBoundary : Laws.addUnitAtPrecisionBoundary := by
  unfold Laws.addUnitAtPrecisionBoundary
  decide

theorem addUnitBelowPrecisionBoundary : Laws.addUnitBelowPrecisionBoundary := by
  unfold Laws.addUnitBelowPrecisionBoundary
  decide

theorem constantRoundsOnce : Laws.constantRoundsOnce := by
  unfold Laws.constantRoundsOnce
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float32_rounding».float32_rounding.Proofs
