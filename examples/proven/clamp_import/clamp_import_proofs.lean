import clamp_import.clamp_import
import clamp_import.limits.limits_verify

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/clamp_import».Proofs

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/clamp_import/limits» (Min Max)
open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/clamp_import/limits».Checked

theorem clampBounds : Laws.clampBounds := by
  intro value low high ordered
  change low ≤ Min (Max value low) high ∧ Min (Max value low) high ≤ high
  refine ⟨?_, atMostRight (Max value low) high⟩
  rcases Int64.le_total (Max value low) high with below | above
  · rw [leftIdentity _ _ below]
    exact atLeastRight value low
  · rw [rightIdentity _ _ above]
    exact ordered

theorem clampIdempotent : Laws.clampIdempotent := by
  intro value low high ordered
  obtain ⟨lower, upper⟩ := clampBounds value low high ordered
  change Min (Max (Clamp value low high) low) high = Clamp value low high
  rw [leftIdentityMax _ _ lower, leftIdentity _ _ upper]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/proven/clamp_import».Proofs
