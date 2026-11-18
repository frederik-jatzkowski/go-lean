-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import division_precondition.division_precondition_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_precondition».division_precondition

theorem dividePanicFree (x divisor : Int64) (h : divisor ≠ 0) :
    Divide x divisor = some (Int64.ofInt (x.toInt.tdiv divisor.toInt)) := by
  sorry

theorem divideByZeroPanics (x : Int64) : Divide x 0 = none := by
  sorry

theorem negativeDividendTruncates : Divide (-7) 3 = some (-2) := by
  sorry

theorem negativeDivisorTruncates : Divide 7 (-3) = some (-2) := by
  sorry

theorem minDividedByNegativeOne : Divide Int64.minValue (-1) = some Int64.minValue := by
  sorry
