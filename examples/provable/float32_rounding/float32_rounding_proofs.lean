import float32_rounding.float32_rounding_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float32_rounding».float32_rounding

theorem addUnitAtPrecisionBoundary : (AddUnit 16777216 == (16777216 : Float32)) = true := by
  decide

theorem addUnitBelowPrecisionBoundary : (AddUnit 16777215 == (16777216 : Float32)) = true := by
  decide

theorem constantRoundsOnce : RoundedConstant.toBits = 0x3f800001 := by
  decide
