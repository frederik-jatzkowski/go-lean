import integer_remainder.integer_remainder_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/integer_remainder».integer_remainder.Proofs

theorem dayBounds : Laws.dayBounds := by
  intro elapsed
  refine ⟨elapsed % 30 + 1, ?_, ?_⟩
  · simp [DayOfMonth]
  · rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
    simp [UInt64.toNat_ofNat]
    omega

theorem monthRollover : Laws.monthRollover := by
  unfold Laws.monthRollover
  decide

theorem signedRemainder : Laws.signedRemainder := by
  unfold Laws.signedRemainder
  decide

theorem minimumByNegativeOne : Laws.minimumByNegativeOne := by
  unfold Laws.minimumByNegativeOne
  decide

theorem zeroPeriodPanics : Laws.zeroPeriodPanics := by
  intro offset
  rfl

theorem zeroPeriodFallback : Laws.zeroPeriodFallback := by
  intro offset
  rfl

theorem nonzeroPeriod : Laws.nonzeroPeriod := by
  intro offset period h
  simp [OffsetOrZero, OffsetInPeriod, h]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/integer_remainder».integer_remainder.Proofs
