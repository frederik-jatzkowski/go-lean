import lower.ssa_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».ssa
open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».ssa.InterfaceContracts

theorem lookupAfterBinding {S : Type} (store : StateStoreContract S)
    (state : S) (value binder : Int64) :
    lookupBindingID store (store.Bind state value binder) value = (binder, true) := by
  simp [lookupBindingID, store.has_after_bind, store.lookup_after_bind]

theorem interveningBindingsPreserveLookup {S : Type} (store : StateStoreContract S)
    (state : S) (value : Int64) (writes : List (Int64 × Int64))
    (distinct : ∀ entry ∈ writes, value ≠ entry.1) :
    lookupBindingID store (writes.foldl (fun s entry => store.Bind s entry.1 entry.2) state) value =
      lookupBindingID store state value := by
  induction writes generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun e member => distinct e (List.mem_cons_of_mem _ member))]
    obtain ⟨present, lookup⟩ := store.bind_other state entry.1 value entry.2
      (distinct entry (by simp))
    simp [lookupBindingID, present, lookup]

theorem lookupAfterEmission {S : Type} (store : StateStoreContract S)
    (state : S) (function : Int64) (effect : Bool) :
    lookupEmission store (recordEmission store state function effect) function = (effect, true) := by
  cases effect <;> simp [recordEmission, lookupEmission, store.has_after_fact, store.lookup_after_fact]

theorem writingDependencyIndexPreservesEmission {S : Type} (store : StateStoreContract S)
    (state : S) (function callee dependencyIndex : Int64) :
    lookupEmission store (store.PutFact state function 1 dependencyIndex) callee =
      lookupEmission store state callee := by
  obtain ⟨present, lookup⟩ := store.fact_other state function 1 callee 0 dependencyIndex
    (Or.inr (by decide))
  simp [lookupEmission, present, lookup]

theorem interveningEmissionsPreserveCallee {S : Type} (store : StateStoreContract S)
    (state : S) (callee : Int64) (effect : Bool) (later : List (Int64 × Bool))
    (distinct : ∀ entry ∈ later, callee ≠ entry.1) :
    lookupEmission store
      (later.foldl (fun s entry => recordEmission store s entry.1 entry.2)
        (recordEmission store state callee effect)) callee = (effect, true) := by
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
