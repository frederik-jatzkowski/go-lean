import division_guarded.division_guarded_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_guarded».division_guarded.Proofs

theorem divideOrZero : Laws.divideOrZero := by
  intro x fallback
  simp [DivideOr]

theorem divideOrNonzero : Laws.divideOrNonzero := by
  intro x divisor fallback h
  simp [DivideOr, h]

theorem divideOrPanicFree : Laws.divideOrPanicFree := by
  intro x divisor fallback
  by_cases h : divisor = 0
  · subst divisor
    exact ⟨fallback, divideOrZero x fallback⟩
  · exact ⟨_, divideOrNonzero x divisor fallback h⟩

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_guarded».division_guarded.Proofs
