-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import division_guarded.division_guarded_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_guarded».division_guarded

theorem divideOrPanicFree (x divisor fallback : Int64) :
    ∃ result, DivideOr x divisor fallback = some result := by
  sorry

theorem divideOrZero (x fallback : Int64) : DivideOr x 0 fallback = some fallback := by
  sorry

theorem divideOrNonzero (x divisor fallback : Int64) (h : divisor ≠ 0) :
    DivideOr x divisor fallback = some (Int64.ofInt (x.toInt.tdiv divisor.toInt)) := by
  sorry
