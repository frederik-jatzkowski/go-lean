import slice_bounds.slice_bounds_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_bounds».slice_bounds.Proofs

theorem validIndexReadsElement : Laws.validIndexReadsElement := by
  intro xs i low
  simp [At, Int.not_lt.mpr low]

theorem validIndexPanicFree : Laws.validIndexPanicFree := by
  intro xs i low high
  have within : i.toInt.toNat < xs.length := (Int.toNat_lt low).mpr high
  rw [validIndexReadsElement xs i low]
  exact ⟨xs[i.toInt.toNat], getElem?_pos xs i.toInt.toNat within⟩

theorem invalidIndexPanics : Laws.invalidIndexPanics := by
  intro xs i outside
  rcases outside with negative | high
  · simp [At, negative]
  · have low : 0 ≤ i.toInt := Int.le_trans (Int.natCast_nonneg xs.length) high
    rw [validIndexReadsElement xs i low]
    exact List.getElem?_eq_none ((Int.le_toNat low).mpr high)

theorem discardedAddressStillPanics : Laws.discardedAddressStillPanics := by
  rfl

theorem maxUnsignedIndexIsOutOfRange : Laws.maxUnsignedIndexIsOutOfRange := by
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_bounds».slice_bounds.Proofs
