import multi_result.multi_result_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/multi_result».multi_result.Proofs

theorem reordersAllResults : Laws.reordersAllResults := by
  unfold Laws.reordersAllResults
  decide

theorem laterResultPanicAbortsCall : Laws.laterResultPanicAbortsCall := by
  intro x
  simp [Reorder, First, Discard, Divide]

theorem concreteReceiverResults : Laws.concreteReceiverResults := by
  unfold Laws.concreteReceiverResults
  decide

theorem statefulCallsThreadReceiver : Laws.statefulCallsThreadReceiver := by
  rfl

theorem loopAndRecursiveResults : Laws.loopAndRecursiveResults := by
  unfold Laws.loopAndRecursiveResults
  decide

theorem distinctFreshMaps : Laws.distinctFreshMaps := by
  unfold Laws.distinctFreshMaps
  decide

theorem freshSliceResults : Laws.freshSliceResults := by
  unfold Laws.freshSliceResults
  decide

theorem effectfulSliceResults : Laws.effectfulSliceResults := by
  unfold Laws.effectfulSliceResults
  decide

theorem statefulLoopResults : Laws.statefulLoopResults := by
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/multi_result».multi_result.Proofs
