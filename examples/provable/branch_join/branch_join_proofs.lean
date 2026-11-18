-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import branch_join.branch_join_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/branch_join».branch_join

theorem branchAssignmentReachesJoin (first second : Int64) :
    PickThenIncrement first second = (if first < second then first else second) + 1 := by
  sorry
