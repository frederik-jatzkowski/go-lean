import division_guarded.division_guarded_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_guarded».division_guarded

theorem divideOrZero (x fallback : Int64) : DivideOr x 0 fallback = some fallback := by
  simp [DivideOr]

theorem divideOrNonzero (x divisor fallback : Int64) (h : divisor ≠ 0) :
    DivideOr x divisor fallback = some (Int64.ofInt (x.toInt.tdiv divisor.toInt)) := by
  simp [DivideOr, h]

theorem divideOrPanicFree (x divisor fallback : Int64) :
    ∃ result, DivideOr x divisor fallback = some result := by
  by_cases h : divisor = 0
  · subst divisor
    exact ⟨fallback, divideOrZero x fallback⟩
  · exact ⟨_, divideOrNonzero x divisor fallback h⟩
