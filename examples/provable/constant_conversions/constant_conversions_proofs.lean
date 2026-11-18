-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import constant_conversions.constant_conversions_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/constant_conversions».constant_conversions

-- This draft models Count with its underlying signed representation.
theorem addsPackageConstant (x : Int64) : Adjusted x = x + 7 := by
  sorry

theorem namedInputWraps : Adjusted Int64.maxValue = Int64.minValue + 6 := by
  sorry
