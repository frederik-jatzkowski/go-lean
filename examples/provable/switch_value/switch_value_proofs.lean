-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import switch_value.switch_value_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_value».switch_value

theorem firstTwoTiers (tier : Int64) (h : tier = 1 ∨ tier = 2) : Rate tier = 5 := by
  sorry

theorem thirdTier : Rate 3 = 8 := by
  sorry

theorem unmatchedTier (tier : Int64) (h₁ : tier ≠ 1) (h₂ : tier ≠ 2) (h₃ : tier ≠ 3) :
    Rate tier = 0 := by
  sorry
