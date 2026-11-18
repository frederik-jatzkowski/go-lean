-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import switch_tagless.switch_tagless_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_tagless».switch_tagless

theorem negativeMatchesFirst (x : Int64) (negative : x < 0) : Bucket x = -1 := by
  sorry

theorem smallNonnegativeMatchesSecond (x : Int64) (low : 0 ≤ x) (high : x < 10) :
    Bucket x = 0 := by
  sorry

theorem largeMatchesDefault (x : Int64) (high : 10 ≤ x) : Bucket x = 1 := by
  sorry
