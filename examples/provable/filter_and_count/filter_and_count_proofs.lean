import filter_and_count.filter_and_count_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/filter_and_count».filter_and_count.Proofs

private def emptyKey := ByteArray.mk #[]

private abbrev Counts := List (ByteArray × GoTypes.Int)

private def step (acc : List ByteArray × Counts) (key : ByteArray) : List ByteArray × Counts :=
  if key == emptyKey then acc else
    let count := (List.lookup key acc.2).getD 0 + 1
    (key :: acc.1, (key, count) :: acc.2.filter (fun entry => !(key == entry.1)))

private def keep (keys : List ByteArray) := keys.filter (fun key => !(key == emptyKey))

private theorem retained (keys : List ByteArray) (acc : List ByteArray × Counts) :
    (keys.foldl step acc).1.reverse = acc.1.reverse ++ keep keys := by
  induction keys generalizing acc with
  | nil => simp [keep]
  | cons key tail ih =>
    rw [List.foldl_cons, ih]
    by_cases h : key = emptyKey <;> simp [step, keep, h, List.append_assoc]

private theorem lookupFiltered (counts : Counts) {key removed : ByteArray} (h : key ≠ removed) :
    List.lookup key (counts.filter (fun entry => !(removed == entry.1))) = List.lookup key counts := by
  induction counts with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨entryKey, count⟩
    by_cases hr : removed = entryKey
    · subst removed
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr h, ih]
    · simp [List.lookup_cons, hr, ih]

private def expected (count : Nat) : Option GoTypes.Int :=
  if count = 0 then none else some ((OfNat.ofNat count : GoTypes.Int))

private theorem counted (keys : List ByteArray) (acc : List ByteArray × Counts)
    (key : ByteArray) (prior : Nat) (h : List.lookup key acc.2 = expected prior) :
    List.lookup key (keys.foldl step acc).2 = expected (prior + (keep keys).count key) := by
  induction keys generalizing acc prior with
  | nil => simpa [keep] using h
  | cons head tail ih =>
    rw [List.foldl_cons]
    by_cases dropped : head = emptyKey
    · simpa [step, keep, dropped] using ih acc prior h
    have kept : (keep (head :: tail)).count key = (head :: keep tail).count key := by
      simp [keep, dropped]
    rw [kept]
    by_cases same : head = key
    · subst head
      have successor : (OfNat.ofNat (prior + 1) : GoTypes.Int) =
          (OfNat.ofNat prior : GoTypes.Int) + 1 := by
        first | exact Int64.ofNat_add _ _ | exact Int32.ofNat_add _ _
      have updated : List.lookup key (step acc key).2 = expected (prior + 1) := by
        simp [step, dropped, h, expected, successor]
        split <;> rename_i isZero
        · subst prior
          rfl
        · simp_all
      simpa [List.count_cons_self, Nat.add_assoc, Nat.add_comm 1] using ih (step acc key) (prior + 1) updated
    · have other : key ≠ head := Ne.symm same
      have updated : List.lookup key (step acc head).2 = expected prior := by
        simpa [step, dropped, List.lookup_cons, beq_eq_false_iff_ne.mpr other, lookupFiltered _ other] using h
      simpa [List.count_cons_of_ne same] using ih (step acc head) prior updated

theorem filtersAndCounts : Laws.filtersAndCounts := by
  intro input
  let keys := (input.getD ([], 0)).1
  change some ((keys.foldl step ([], [])).1.reverse, keys.length) = some (keep keys, keys.length) ∧
    ∀ key, List.lookup key (keys.foldl step ([], [])).2 = expected ((keep keys).count key)
  constructor
  · simp [retained]
  · intro key
    simpa using counted keys ([], []) key 0 (by simp [expected])

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/filter_and_count».filter_and_count.Proofs
