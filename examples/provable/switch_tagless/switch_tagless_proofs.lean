import switch_tagless.switch_tagless_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_tagless».switch_tagless.Proofs

theorem negativeMatchesFirst : Laws.negativeMatchesFirst := by
  intro x negative
  simp [Bucket, negative]

theorem smallNonnegativeMatchesSecond : Laws.smallNonnegativeMatchesSecond := by
  intro x low high
  simp [Bucket, Int64.not_lt.mpr low, high]

theorem largeMatchesDefault : Laws.largeMatchesDefault := by
  intro x high
  have low : 0 ≤ x := Int64.le_trans (by decide : (0 : Int64) ≤ 10) high
  simp [Bucket, Int64.not_lt.mpr low, Int64.not_lt.mpr high]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_tagless».switch_tagless.Proofs
