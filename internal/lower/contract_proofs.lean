import lower.contract_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».contract.Proofs
open GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».contract.InterfaceContracts

theorem resolvedOperandIsPresent : Laws.resolvedOperandIsPresent := by
  intro I S input store source state phi pred found
  by_cases incoming : input.HasIncoming source phi pred = true
  · by_cases bound : store.HasBinding state (input.Incoming source phi pred) = true
    · simpa [resolveIncoming, incoming, bound] using input.incoming_exists source phi pred incoming
    · simpa [resolveIncoming, incoming, bound] using input.incoming_exists source phi pred incoming
  · simp [resolveIncoming, incoming] at found

theorem resolvesPhiOfCurrentPredecessor : Laws.resolvesPhiOfCurrentPredecessor := by
  intro I S input store source current phi pred position low high predecessor bound
  obtain ⟨incoming, aligned⟩ := input.incoming_alignment source phi pred position low high predecessor
  simp [resolveIncoming, incoming, aligned, bound]

theorem resolvesBranchBinding : Laws.resolvesBranchBinding := by
  intro I S input store source parent phi pred value binder incoming selected
  simp [resolveIncoming, incoming, selected, store.has_after_bind, store.lookup_after_bind]

theorem branchUpdatePreservesSiblingResolution : Laws.branchUpdatePreservesSiblingResolution := by
  intro I S input store source parent phi sibling key binder distinct
  obtain ⟨has, lookup⟩ := store.bind_other parent key (input.Incoming source phi sibling) binder distinct
  simp [resolveIncoming, has, lookup]

theorem carryingCursorPreservesIncomingResolution : Laws.carryingCursorPreservesIncomingResolution := by
  intro I S input store source parent phi pred cursor
  obtain ⟨has, lookup⟩ := store.cursor_preserves_bindings parent cursor (input.Incoming source phi pred)
  simp [resolveIncoming, has, lookup]

end GoLean.«github.com/frederik-jatzkowski/go-lean/internal/lower».contract.Proofs
