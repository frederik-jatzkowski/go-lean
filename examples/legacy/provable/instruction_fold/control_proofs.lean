import instruction_fold.control_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/instruction_fold».control.Proofs

theorem controlPaths : Laws.controlPaths := by
  unfold Laws.controlPaths
  decide

theorem arraySnapshot : Laws.arraySnapshot := by
  unfold Laws.arraySnapshot
  decide

theorem loopCallPropagatesPanic : Laws.loopCallPropagatesPanic := by
  unfold Laws.loopCallPropagatesPanic
  decide

theorem checkedLoopIndex : Laws.checkedLoopIndex := by
  unfold Laws.checkedLoopIndex
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/instruction_fold».control.Proofs
