import integer_remainder.integer_remainder_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/integer_remainder».integer_remainder

theorem dayBounds (elapsed : UInt64) :
    ∃ day, DayOfMonth elapsed = some day ∧ 1 ≤ day ∧ day ≤ 30 := by
  refine ⟨elapsed % 30 + 1, ?_, ?_⟩
  · simp [DayOfMonth]
  · rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le]
    simp [UInt64.toNat_ofNat]
    omega

theorem monthRollover :
    DayOfMonth 29 = some 30 ∧ DayOfMonth 30 = some 1 := by
  decide

theorem signedRemainder :
    OffsetInPeriod (-7) 3 = some (-1) ∧ OffsetInPeriod 7 (-3) = some 1 := by
  decide

theorem minimumByNegativeOne :
    OffsetInPeriod (-9223372036854775808) (-1) = some 0 := by
  decide

theorem zeroPeriodPanics (offset : Int64) : OffsetInPeriod offset 0 = none := by
  rfl

theorem zeroPeriodFallback (offset : Int64) : OffsetOrZero offset 0 = some 0 := by
  rfl

theorem nonzeroPeriod (offset period : Int64) (h : period ≠ 0) :
    OffsetOrZero offset period = some (offset % period) := by
  simp [OffsetOrZero, OffsetInPeriod, h]
