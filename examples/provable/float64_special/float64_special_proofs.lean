-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import float64_special.float64_special_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float64_special».float64_special

theorem detectsNaN (x : Float) : IsNaN x = x.isNaN := by
  sorry

theorem nanIsUnordered (x y : Float) (h : x.isNaN = true ∨ y.isNaN = true) :
    Less x y = false := by
  sorry
