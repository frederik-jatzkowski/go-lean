import multi_result.multi_result_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/multi_result».multi_result

theorem reordersAllResults :
    Reorder (-12) 3 = some (true, (-4, -12)) := by
  decide

theorem laterResultPanicAbortsCall (x : Int64) :
    Reorder x 0 = none ∧ First x 0 = none ∧ Discard x 0 = none := by
  simp [Reorder, First, Discard, Divide]

theorem concreteReceiverResults :
    «Counter$Read» ⟨-3⟩ = (-3, true) ∧
    «Counter$Peek» (some ⟨4⟩) = some (4, false) ∧
    «Counter$Peek» none = none := by
  decide

theorem statefulCallsThreadReceiver :
    «Counter$AddTwice» (some ⟨3⟩) 2 = some (some ⟨7⟩, (3, 7)) := by
  rfl

theorem loopAndRecursiveResults :
    Count 4 = (4, 8) ∧ Fold [7, -1, 2] = (3, 8) ∧ Chain [7, -1, 2] = (3, 8) := by
  decide

theorem distinctFreshMaps :
    ForwardMaps 5 = some ([(5, 1)], (true, [(5, 2)])) := by
  decide

theorem freshSliceResults :
    ForwardSlice [3, 5] = some ([3, 5], 2) ∧ Double [3, 5] = some (2, [6, 10]) := by
  decide

theorem effectfulSliceResults :
    Reciprocals [3, 6] = some ([4, 2], 2) ∧ Reciprocals [3, 0] = none := by
  decide

theorem statefulLoopResults :
    «Queue$Drain» (some ⟨0, some [3, 6], 1⟩) =
      some (some ⟨2, some [3, 6], 10⟩, (10, 2)) := by
  rfl
