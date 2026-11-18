-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import narrow_signed.narrow_signed_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/narrow_signed».narrow_signed

theorem increment8Wraps : Increment8 Int8.maxValue = Int8.minValue := by
  sorry

theorem increment16Wraps : Increment16 Int16.maxValue = Int16.minValue := by
  sorry

theorem increment32Wraps : Increment32 Int32.maxValue = Int32.minValue := by
  sorry
