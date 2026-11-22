import switch_value.switch_value_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_value».switch_value.Proofs

theorem firstTwoTiers : Laws.firstTwoTiers := by
  intro tier h
  rcases h with rfl | rfl <;> decide

theorem thirdTier : Laws.thirdTier := by
  unfold Laws.thirdTier
  decide

theorem unmatchedTier : Laws.unmatchedTier := by
  intro tier h₁ h₂ h₃
  simp [Rate, h₁, h₂, h₃]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/switch_value».switch_value.Proofs
