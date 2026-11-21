import local_array_loop.occupancy_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/local_array_loop».occupancy.Proofs

private abbrev Table := Vector Bool 30
private abbrev Zero : Table := Vector.replicate 30 false
private abbrev Valid (slot : GoTypes.Int) := 0 ≤ slot.toInt ∧ slot.toInt < 30
private abbrev Fits (n : Nat) := (n : Int) < 2 ^ (GoTypes.WordBits - 1)
private abbrev After (n : Nat) : GoTypes.Int := .ofInt ((n : Int) - 1)

private theorem initialCounter : After 0 = .ofInt (-1) := by
  unfold After
  rw [show ((0 : Nat) : Int) - 1 = -1 by omega]

private theorem counterStep (n : Nat) : After n + .ofInt 1 = .ofNat n := by
  unfold After
  first | rw [← Int64.ofInt_add] | rw [← Int32.ofInt_add]
  rw [Int.sub_add_cancel]
  rfl

private theorem nextState (n : Nat) : After (n + 1) = .ofNat n := by
  unfold After
  rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega]
  rfl

private theorem counterValue {n : Nat} (h : Fits n) : (.ofNat n : GoTypes.Int).toInt = n := by
  change (.ofInt (n : Int) : GoTypes.Int).toInt = n
  first
  | exact Int64.toInt_ofInt_of_le (by omega) h
  | exact Int32.toInt_ofInt_of_le (by omega) h

private theorem readArray (a : Table) (slot : GoTypes.Int) (h : Valid slot) :
    a.toArray[slot.toInt.toNat]? = some (a.get ⟨slot.toInt.toNat, by omega⟩) := by
  rw [Array.getElem?_eq_getElem (by simpa using (show slot.toInt.toNat < 30 by omega))]
  rfl

theorem readsSlot : Laws.readsSlot := by
  intro occupied slot low high
  simp only [isOccupied, Int.not_lt.mpr low, ite_false, readArray occupied slot ⟨low, high⟩,
    bind, Option.bind, pure]

private def markList : List GoTypes.Int → Table → Option Table
  | [], a => some a
  | slot :: rest, a =>
    if Valid slot then markList rest (a.setIfInBounds slot.toInt.toNat true) else none

private theorem markLoop (slots : List GoTypes.Int) (fits : Fits slots.length)
    (fuel n : Nat) (remaining : n + fuel = slots.length) (a : Table) :
    markOccupied.«v4_loop» slots (.ofNat slots.length) fuel (After n, a) =
      markList (slots.drop n) a := by
  induction fuel generalizing n a with
  | zero =>
    have done := List.drop_eq_nil_of_le (as := slots) (i := n) (by omega)
    rw [done]; rfl
  | succ fuel ih =>
    have hn : n < slots.length := by omega
    have fitsN : Fits n := Int.lt_trans (by omega : (n : Int) < slots.length) fits
    let slot := slots[n]
    have read : slots[n]? = some slot := List.getElem?_eq_getElem hn
    have nonneg : ¬ (n : Int) < 0 := by omega
    have atIndex : (n : Int).toNat = n := Int.toNat_natCast n
    rw [List.drop_eq_getElem_cons hn]
    change _ = markList (slot :: slots.drop (n + 1)) a
    by_cases valid : Valid slot
    · have next := ih (n + 1) (by omega) (a.setIfInBounds slot.toInt.toNat true)
      rw [markList, ite_eq_left valid]
      simp only [markOccupied.«v4_loop», counterStep, counterValue fitsN, nonneg, ite_false, atIndex,
        read, Int.not_lt.mpr valid.1, readArray a slot valid, bind, Option.bind]
      rw [nextState] at next
      exact next
    · by_cases low : slot.toInt < 0
      · rw [markList, ite_eq_right valid]
        simp only [markOccupied.«v4_loop», counterStep, counterValue fitsN, nonneg, ite_false, atIndex,
          read, low, ite_true, bind, Option.bind]
      · have outside : a.toArray.size ≤ slot.toInt.toNat := by
          simp only [Vector.size_toArray]
          unfold Valid at valid
          omega
        rw [markList, ite_eq_right valid]
        simp only [markOccupied.«v4_loop», counterStep, counterValue fitsN, nonneg, ite_false, atIndex,
          read, low, Array.getElem?_eq_none outside, bind, Option.bind]

private theorem markModel (slots : List GoTypes.Int) (fits : Fits slots.length) :
    markOccupied slots = markList slots Zero := by
  simpa only [markOccupied, counterValue fits, Int.toNat_natCast, List.drop_zero, initialCounter] using markLoop slots fits slots.length 0 (by simp) Zero

private theorem markListExact (slots : List GoTypes.Int) (a : Table)
    (valid : ∀ slot ∈ slots, Valid slot) :
    ∃ out, markList slots a = some out ∧ ∀ i : Fin 30,
      out[i] = true ↔ a[i] = true ∨ ∃ slot ∈ slots, slot.toInt = i.val := by
  induction slots generalizing a with
  | nil => exact ⟨a, rfl, by simp⟩
  | cons slot rest ih =>
    have h := valid slot (by simp)
    obtain ⟨out, run, exactness⟩ := ih (a.setIfInBounds slot.toInt.toNat true)
      (fun s mem => valid s (by simp [mem]))
    refine ⟨out, by rw [markList, ite_eq_left h]; exact run, fun i => ?_⟩
    rw [exactness i]
    change ((a.setIfInBounds slot.toInt.toNat true)[i.val] = true ∨ _) ↔ _
    rw [Vector.getElem_setIfInBounds i.isLt]
    have index : slot.toInt.toNat = i.val ↔ slot.toInt = i.val := by
      have := h.1
      omega
    by_cases same : slot.toInt.toNat = i.val
    · rw [ite_eq_left same]
      simp [index.mp same]
    · have different : slot.toInt ≠ i.val := fun eq => same (index.mpr eq)
      rw [ite_eq_right same]
      simp [different]

private theorem markListPanics (slots : List GoTypes.Int) (a : Table)
    (bad : ∃ slot ∈ slots, ¬ Valid slot) : markList slots a = none := by
  induction slots generalizing a with
  | nil => simp at bad
  | cons slot rest ih =>
    by_cases h : Valid slot
    · rw [markList, ite_eq_left h]
      apply ih
      obtain ⟨s, mem, invalid⟩ := bad
      rcases List.mem_cons.mp mem with rfl | tail
      · exact (invalid h).elim
      · exact ⟨s, tail, invalid⟩
    · rw [markList, ite_eq_right h]

theorem marksExactly : Laws.marksExactly := by
  intro slots fits valid
  rw [markModel slots fits]
  obtain ⟨out, run, exactness⟩ := markListExact slots Zero valid
  exact ⟨out, run, by simpa using exactness⟩

theorem badSlotPanics : Laws.badSlotPanics := by
  intro slots fits bad
  rw [markModel slots fits]
  obtain ⟨slot, mem, outside⟩ := bad
  exact markListPanics slots Zero ⟨slot, mem, by unfold Valid; omega⟩

private theorem observeLoop (slots : List GoTypes.Int) (fits : Fits slots.length)
    (valid : ∀ slot ∈ slots, Valid slot) (fuel n : Nat) (remaining : n + fuel = slots.length) :
    observeAndClear.«v4_loop» slots (.ofNat slots.length) fuel (true, After n, Zero) =
      some (Zero, true) := by
  induction fuel generalizing n with
  | zero => simp [observeAndClear.«v4_loop»]
  | succ fuel ih =>
    have hn : n < slots.length := by omega
    have fitsN : Fits n := Int.lt_trans (by omega : (n : Int) < slots.length) fits
    let slot := slots[n]
    have read : slots[n]? = some slot := List.getElem?_eq_getElem hn
    have h := valid slot (List.getElem_mem hn)
    have checked := readsSlot (Zero.setIfInBounds slot.toInt.toNat true) slot h.1 h.2
    have hi : slot.toInt.toNat < 30 := by have := h.1; have := h.2; omega
    have seen : isOccupied (Zero.setIfInBounds slot.toInt.toNat true) slot = some true := by
      rw [checked]
      congr 1
      change (Zero.setIfInBounds slot.toInt.toNat true)[slot.toInt.toNat] = true
      exact Vector.getElem_setIfInBounds_self hi
    have next := ih (n + 1) (by omega)
    have nonneg : ¬ (n : Int) < 0 := by omega
    have atIndex : (n : Int).toNat = n := Int.toNat_natCast n
    rw [nextState] at next
    simpa only [observeAndClear.«v4_loop», counterStep, counterValue fitsN, nonneg, ite_false, atIndex, read,
      Int.not_lt.mpr h.1, readArray Zero slot h, readArray (Zero.setIfInBounds slot.toInt.toNat true) slot h,
      seen, ite_true, bind, Option.bind, Vector.setIfInBounds_setIfInBounds, Vector.setIfInBounds_replicate_self] using next

theorem seesCurrentState : Laws.seesCurrentState := by
  intro slots fits valid
  simpa only [observeAndClear, counterValue fits, Int.toNat_natCast, initialCounter] using observeLoop slots fits valid slots.length 0 (by simp)

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/local_array_loop».occupancy.Proofs
