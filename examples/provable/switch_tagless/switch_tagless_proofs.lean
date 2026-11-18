import switch_tagless.switch_tagless_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_tagless».switch_tagless

theorem negativeMatchesFirst (x : Int64) (negative : x < 0) : Bucket x = -1 := by
  simp [Bucket, negative]

theorem smallNonnegativeMatchesSecond (x : Int64) (low : 0 ≤ x) (high : x < 10) :
    Bucket x = 0 := by
  simp [Bucket, Int64.not_lt.mpr low, high]

theorem largeMatchesDefault (x : Int64) (high : 10 ≤ x) : Bucket x = 1 := by
  have low : 0 ≤ x := Int64.le_trans (by decide : (0 : Int64) ≤ 10) high
  simp [Bucket, Int64.not_lt.mpr low, Int64.not_lt.mpr high]
