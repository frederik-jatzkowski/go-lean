import branch_join.branch_join_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/branch_join».branch_join.Proofs

theorem branchAssignmentReachesJoin : Laws.branchAssignmentReachesJoin := by
  intro first second
  by_cases h : first < second <;> simp [PickThenIncrement, h]

theorem skippedDivisionReachesJoin : Laws.skippedDivisionReachesJoin := by
  intro value
  rfl

theorem divisionPanicSkipsJoin : Laws.divisionPanicSkipsJoin := by
  intro value
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/branch_join».branch_join.Proofs
