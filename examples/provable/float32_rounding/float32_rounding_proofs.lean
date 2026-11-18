-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import float32_rounding.float32_rounding_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float32_rounding».float32_rounding

theorem addUnitAtPrecisionBoundary : (AddUnit 16777216 == (16777216 : Float32)) = true := by
  sorry

theorem addUnitBelowPrecisionBoundary : (AddUnit 16777215 == (16777216 : Float32)) = true := by
  sorry
