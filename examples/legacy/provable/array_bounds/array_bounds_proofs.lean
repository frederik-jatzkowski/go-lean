import array_bounds.array_bounds_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/array_bounds».array_bounds.Proofs

private theorem wordLt {a b : GoTypes.Int} : a < b ↔ a.toInt < b.toInt := by
  first | exact Int64.lt_iff_toInt_lt | exact Int32.lt_iff_toInt_lt

private theorem wordLe {a b : GoTypes.Int} : a ≤ b ↔ a.toInt ≤ b.toInt := by
  first | exact Int64.le_iff_toInt_le | exact Int32.le_iff_toInt_le

theorem guardedIndexInBounds : Laws.guardedIndexInBounds := by
  intro xs i fallback low high
  have nonnegative := Int.not_lt.mpr low
  have lower : ¬ i < 0 := fun h => nonnegative (wordLt.mp h)
  have upper : ¬ (4 : GoTypes.Int) ≤ i := fun h => Int.not_le.mpr high (wordLe.mp h)
  simp [AtOr, lower, upper, nonnegative]

theorem guardedIndexFallback : Laws.guardedIndexFallback := by
  intro xs i fallback outside
  rcases outside with negative | high
  · have h : i < 0 := wordLt.mpr negative
    simp [AtOr, h]
  · have h : (4 : GoTypes.Int) ≤ i := wordLe.mpr high
    by_cases low : i < 0 <;> simp [AtOr, low, h]

theorem guardedIndexPanicFree : Laws.guardedIndexPanicFree := by
  intro xs i fallback
  by_cases low : 0 ≤ i.toInt
  · by_cases high : i.toInt < 4
    · have within : i.toInt.toNat < xs.toArray.size := by
        rw [xs.size_toArray]
        exact (Int.toNat_lt low).mpr high
      rw [guardedIndexInBounds xs i fallback low high]
      exact ⟨xs.toArray[i.toInt.toNat], getElem?_pos xs.toArray i.toInt.toNat within⟩
    · exact ⟨fallback, guardedIndexFallback xs i fallback (.inr (Int.not_lt.mp high))⟩
  · exact ⟨fallback, guardedIndexFallback xs i fallback (.inl (Int.not_le.mp low))⟩

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/array_bounds».array_bounds.Proofs
