import lower.ssa_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».ssa.Proofs
open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».ssa.InterfaceContracts

theorem lookupAfterBinding : Laws.lookupAfterBinding := by
  intro S store state value binder
  simp [lookupBindingID, store.has_after_bind, store.lookup_after_bind]

theorem interveningBindingsPreserveLookup : Laws.interveningBindingsPreserveLookup := by
  intro S store state value writes distinct
  induction writes generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun e member => distinct e (List.mem_cons_of_mem _ member))]
    obtain ⟨present, lookup⟩ := store.bind_other state entry.1 value entry.2
      (distinct entry (by simp))
    simp [lookupBindingID, present, lookup]

theorem lookupAfterEmission : Laws.lookupAfterEmission := by
  intro S store state function effect
  cases effect <;> simp [recordEmission, lookupEmission, store.has_after_fact, store.lookup_after_fact]

theorem writingDependencyIndexPreservesEmission : Laws.writingDependencyIndexPreservesEmission := by
  intro S store state function callee dependencyIndex
  obtain ⟨present, lookup⟩ := store.fact_other state function 1 callee 0 dependencyIndex
    (Or.inr (by decide))
  simp [lookupEmission, present, lookup]

theorem interveningEmissionsPreserveCallee : Laws.interveningEmissionsPreserveCallee := by
  intro S store state callee effect later distinct
  suffices preserves : ∀ current,
      lookupEmission store (later.foldl (fun s entry => recordEmission store s entry.1 entry.2)
        current) callee = lookupEmission store current callee by
    rw [preserves, lookupAfterEmission]
  induction later with
  | nil => intro current; rfl
  | cons entry rest ih =>
    intro current
    simp only [List.foldl_cons]
    rw [ih (fun e member => distinct e (List.mem_cons_of_mem _ member))]
    have other : callee ≠ entry.1 := distinct entry (by simp)
    have preserve (v : Int64) :
        lookupEmission store (store.PutFact current entry.1 0 v) callee =
          lookupEmission store current callee := by
      obtain ⟨present, lookup⟩ := store.fact_other current entry.1 0 callee 0 v (Or.inl other)
      simp [lookupEmission, present, lookup]
    cases h : entry.2 <;> simpa [recordEmission, h] using preserve (if entry.2 then 1 else 0)

end GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».ssa.Proofs
