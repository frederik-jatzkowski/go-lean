import slice_bounds.slice_bounds_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_bounds».slice_bounds

theorem validIndexReadsElement (xs : List Int64) (i : GoTypes.Int) (low : 0 ≤ i.toInt) :
    At xs i = xs[i.toInt.toNat]? := by
  simp [At, Int.not_lt.mpr low]

theorem validIndexPanicFree (xs : List Int64) (i : GoTypes.Int)
    (low : 0 ≤ i.toInt) (high : i.toInt < Int.ofNat xs.length) :
    ∃ result, At xs i = some result := by
  have within : i.toInt.toNat < xs.length := (Int.toNat_lt low).mpr high
  rw [validIndexReadsElement xs i low]
  exact ⟨xs[i.toInt.toNat], getElem?_pos xs i.toInt.toNat within⟩

theorem invalidIndexPanics (xs : List Int64) (i : GoTypes.Int)
    (outside : i.toInt < 0 ∨ Int.ofNat xs.length ≤ i.toInt) :
    At xs i = none := by
  rcases outside with negative | high
  · simp [At, negative]
  · have low : 0 ≤ i.toInt := Int.le_trans (Int.natCast_nonneg xs.length) high
    rw [validIndexReadsElement xs i low]
    exact List.getElem?_eq_none ((Int.le_toNat low).mpr high)

theorem discardedAddressStillPanics : Touch [] 0 = none := by
  rfl

theorem maxUnsignedIndexIsOutOfRange : AtUnsigned [42] 0xffffffffffffffff = none := by
  rfl
