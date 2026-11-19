import division_precondition.division_precondition_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_precondition».division_precondition.Proofs

theorem dividePanicFree : Laws.dividePanicFree := by
  intro x divisor h
  simp [Divide, h]

theorem divideByZeroPanics : Laws.divideByZeroPanics := by
  intro x
  simp [Divide]

theorem negativeDividendTruncates : Laws.negativeDividendTruncates := by
  unfold Laws.negativeDividendTruncates
  decide

theorem negativeDivisorTruncates : Laws.negativeDivisorTruncates := by
  unfold Laws.negativeDivisorTruncates
  decide

theorem minDividedByNegativeOne : Laws.minDividedByNegativeOne := by
  unfold Laws.minDividedByNegativeOne
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_precondition».division_precondition.Proofs
