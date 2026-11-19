import clampimport.clampimport_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clampimport».clampimport.Proofs

theorem clampBounds : Laws.clampBounds := by
  intro minSpec maxSpec
  dsimp only
  intro value low high ordered
  change low ≤ minSpec.operation (maxSpec.operation value low) high ∧
    minSpec.operation (maxSpec.operation value low) high ≤ high
  have minIdentity : ∀ x y, x ≤ y → minSpec.operation x y = x := minSpec.leftIdentity
  have minRight : ∀ x y, y ≤ x → minSpec.operation x y = y := minSpec.rightIdentity
  refine ⟨?_, minSpec.atMostRight (maxSpec.operation value low) high⟩
  rcases Int64.le_total (maxSpec.operation value low) high with below | above
  · rw [minIdentity _ _ below]
    exact maxSpec.atLeastRight value low
  · rw [minRight _ _ above]
    exact ordered

theorem clampIdempotent : Laws.clampIdempotent := by
  intro minSpec maxSpec
  dsimp only
  intro value low high ordered
  obtain ⟨lower, upper⟩ := clampBounds minSpec maxSpec value low high ordered
  have minIdentity : ∀ x y, x ≤ y → minSpec.operation x y = x := minSpec.leftIdentity
  have maxIdentity : ∀ x y, y ≤ x → maxSpec.operation x y = x := maxSpec.leftIdentityMax
  change minSpec.operation (maxSpec.operation (Clamp minSpec maxSpec value low high) low) high =
    Clamp minSpec maxSpec value low high
  rw [maxIdentity _ _ lower, minIdentity _ _ upper]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clampimport».clampimport.Proofs
