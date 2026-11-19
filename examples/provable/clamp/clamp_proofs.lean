import clamp.clamp_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp.Proofs

theorem clampBounds : Laws.clampBounds := by
  intro value low high ordered
  simp only [Clamp, decide_eq_true_eq]
  by_cases below : value < low
  · simpa [below] using ordered
  · by_cases above : high < value
    · simpa [below, above] using ordered
    · simpa [below, above] using And.intro (Int64.not_lt.mp below) (Int64.not_lt.mp above)

private theorem unchanged (value low high : Int64) (lower : low ≤ value) (upper : value ≤ high) :
    Clamp value low high = value := by
  have below := Int64.not_lt.mpr lower
  have above := Int64.not_lt.mpr upper
  simp [Clamp, below, above]

theorem clampIdempotent : Laws.clampIdempotent := by
  intro value low high ordered
  obtain ⟨lower, upper⟩ := clampBounds value low high ordered
  exact unchanged _ _ _ lower upper

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clamp».clamp.Proofs
