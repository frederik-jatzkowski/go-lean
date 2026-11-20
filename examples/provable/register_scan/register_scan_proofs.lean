import register_scan.register_scan_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/register_scan».«register_scan».Proofs

private def Prefix (occupied : Vector Bool 30) (n : Nat) (result : GoTypes.Int) : Prop :=
  (result = -1 ∧ ∀ i : Fin 30, i.val < n → occupied[i] = true) ∨
  (∃ i : Fin 30, i.val < n ∧ result.toInt = i.val ∧ occupied[i] = false ∧
    ∀ j : Fin 30, i < j → j.val < n → occupied[j] = true)

private theorem counterValue (n : Nat) (h : n ≤ 30) :
    (Int64.ofNat n).toInt = n := by
  change (Int64.ofInt ((n : Int))).toInt = n
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

private theorem outOfBoundsPropagates (occupied : Vector Bool 30) :
    «freeRegister$loop» occupied 1 (-1, 30) = none := by
  simp [«freeRegister$loop», bind, Option.bind]

private theorem scan (occupied : Vector Bool 30) (fuel n : Nat) (acc : GoTypes.Int)
    (bound : n + fuel ≤ 30) (inv : Prefix occupied n acc) :
    ∃ result, «freeRegister$loop» occupied fuel (acc, Int64.ofNat n) =
      some (result, Int64.ofNat (n + fuel)) ∧ Prefix occupied (n + fuel) result := by
  induction fuel generalizing n acc with
  | zero => exact ⟨acc, by simp [«freeRegister$loop»], by simpa using inv⟩
  | succ fuel ih =>
    have hn : n < 30 := by omega
    let i : Fin 30 := ⟨n, hn⟩
    have read : occupied.toArray[n]? = some occupied[i] := by
      rw [Array.getElem?_eq_getElem (by simpa using hn)]
      rfl
    have step : Int64.ofNat n + Int64.ofInt 1 = Int64.ofNat (n + 1) := by
      rw [Int64.ofNat_add]
      rfl
    have nonneg : ¬ (n : Int) < 0 := by omega
    have total : n + 1 + fuel = n + (fuel + 1) := by omega
    have advance (next : GoTypes.Int) (h : Prefix occupied (n + 1) next) :=
      ih (n + 1) next (by omega) h
    cases slot : occupied[i] with
    | false =>
      have next : Prefix occupied (n + 1) (Int64.ofNat n) := by
        right
        refine ⟨i, by simp [i], counterValue n (by omega), slot, ?_⟩
        intro j hj hjn
        change n < j.val at hj
        omega
      obtain ⟨result, run, law⟩ := advance _ next
      rw [total] at run law
      refine ⟨result, ?_, law⟩
      simpa [«freeRegister$loop», counterValue n (by omega), read, slot, step,
        nonneg, bind, Option.bind] using run
    | true =>
      have keep (j : Fin 30) (hj : j.val < n + 1)
          (earlier : j.val < n → occupied[j] = true) : occupied[j] = true := by
        by_cases h : j.val < n
        · exact earlier h
        · have eq : j = i := Fin.ext (by change j.val = n; omega)
          simpa [eq] using slot
      have next : Prefix occupied (n + 1) acc := by
        rcases inv with ⟨sentinel, all⟩ | ⟨best, hb, value, free, later⟩
        · exact Or.inl ⟨sentinel, fun j hj => keep j hj (all j)⟩
        · exact Or.inr ⟨best, by omega, value, free, fun j hbj hj => keep j hj (later j hbj)⟩
      obtain ⟨result, run, law⟩ := advance _ next
      rw [total] at run law
      refine ⟨result, ?_, law⟩
      simpa [«freeRegister$loop», counterValue n (by omega), read, slot, step,
        nonneg, bind, Option.bind] using run

theorem selectsHighestFree : Laws.selectsHighestFree := by
  intro occupied
  have initial : Prefix occupied 0 (-1) :=
    Or.inl ⟨rfl, fun i h => by omega⟩
  obtain ⟨result, run, law⟩ := scan occupied 30 0 (-1) (by decide) initial
  refine ⟨result, ?_, ?_, ?_⟩
  · change (do
      let state ← «freeRegister$loop» occupied 30 (-1, Int64.ofNat 0)
      pure state.1) = some result
    rw [run]
    rfl
  · rcases law with ⟨sentinel, all⟩ | ⟨i, _, value, free, _⟩
    · exact ⟨fun _ i => all i i.isLt, fun _ => sentinel⟩
    · constructor
      · intro h
        rw [h] at value
        change (-1 : Int) = i.val at value
        omega
      · intro all
        simp [all i] at free
  · intro found
    rcases law with ⟨sentinel, _⟩ | ⟨i, _, value, free, later⟩
    · exact (found sentinel).elim
    · exact ⟨i, value, free, fun j h => later j h j.isLt⟩

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/register_scan».«register_scan».Proofs
