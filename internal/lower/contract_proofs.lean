import lower.contract_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».contract
open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».contract.InterfaceContracts

theorem resolvedOperandIsPresent {I S : Type}
    (input : InputContract I) (store : StateStoreContract S)
    (source : I) (state : S) (phi pred : Int64)
    (found : (resolveIncoming input store source state phi pred).2.2.1 = true) :
    0 < (resolveIncoming input store source state phi pred).1 := by
  by_cases incoming : input.HasIncoming source phi pred = true
  · by_cases bound : store.HasBinding state (input.Incoming source phi pred) = true
    · simpa [resolveIncoming, incoming, bound] using input.incoming_exists source phi pred incoming
    · simpa [resolveIncoming, incoming, bound] using input.incoming_exists source phi pred incoming
  · simp [resolveIncoming, incoming] at found

theorem resolvesPhiOfCurrentPredecessor {I S : Type}
    (input : InputContract I) (store : StateStoreContract S)
    (source : I) (current : S) (phi pred position : Int64)
    (low : 0 ≤ position) (high : position < input.PredecessorCount source (input.PhiBlock source phi))
    (predecessor : input.PredecessorAt source (input.PhiBlock source phi) position = pred)
    (bound : store.HasBinding current (input.PhiOperandAt source phi position) = true) :
    resolveIncoming input store source current phi pred =
      (input.PhiOperandAt source phi position, (store.LookupBinding current (input.PhiOperandAt source phi position),
        (true, true))) := by
  obtain ⟨incoming, aligned⟩ := input.incoming_alignment source phi pred position low high predecessor
  simp [resolveIncoming, incoming, aligned, bound]

theorem resolvesBranchBinding {I S : Type}
    (input : InputContract I) (store : StateStoreContract S)
    (source : I) (parent : S) (phi pred value binder : Int64)
    (incoming : input.HasIncoming source phi pred = true)
    (selected : input.Incoming source phi pred = value) :
    resolveIncoming input store source (store.Bind parent value binder) phi pred =
      (value, (binder, (true, true))) := by
  simp [resolveIncoming, incoming, selected, store.has_after_bind, store.lookup_after_bind]

theorem branchUpdatePreservesSiblingResolution {I S : Type}
    (input : InputContract I) (store : StateStoreContract S)
    (source : I) (parent : S) (phi sibling key binder : Int64)
    (distinct : input.Incoming source phi sibling ≠ key) :
    resolveIncoming input store source (store.Bind parent key binder) phi sibling =
      resolveIncoming input store source parent phi sibling := by
  obtain ⟨has, lookup⟩ := store.bind_other parent key (input.Incoming source phi sibling) binder distinct
  simp [resolveIncoming, has, lookup]

theorem carryingCursorPreservesIncomingResolution {I S : Type}
    (input : InputContract I) (store : StateStoreContract S)
    (source : I) (parent : S) (phi pred cursor : Int64) :
    resolveIncoming input store source (store.WithCursor parent cursor) phi pred =
      resolveIncoming input store source parent phi pred := by
  obtain ⟨has, lookup⟩ := store.cursor_preserves_bindings parent cursor (input.Incoming source phi pred)
  simp [resolveIncoming, has, lookup]
