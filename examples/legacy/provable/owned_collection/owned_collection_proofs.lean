import owned_collection.owned_collection_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/owned_collection».owned_collection.Proofs

theorem conditionalWrites : Laws.conditionalWrites := by
  unfold Laws.conditionalWrites
  intro length keep
  by_cases valid : length = 2
  · subst length
    cases keep <;> decide
  · cases keep <;> simp [Build, valid, bind, Option.bind] <;> rfl

theorem checkedWrite : Laws.checkedWrite := by
  unfold Laws.checkedWrite
  decide

theorem repeatedMapUpdates : Laws.repeatedMapUpdates := by
  unfold Laws.repeatedMapUpdates
  decide

theorem appendsConsumeView : Laws.appendsConsumeView := by
  unfold Laws.appendsConsumeView
  decide

theorem fixedSizeBuild : Laws.fixedSizeBuild := by
  unfold Laws.fixedSizeBuild
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/owned_collection».owned_collection.Proofs
