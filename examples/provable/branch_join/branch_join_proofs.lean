import branch_join.branch_join_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/branch_join».branch_join

theorem branchAssignmentReachesJoin (first second : Int64) :
    PickThenIncrement first second = (if first < second then first else second) + 1 := by
  by_cases h : first < second <;> simp [PickThenIncrement, h]

theorem skippedDivisionReachesJoin (value : Int64) :
    IncrementWithOptionalQuotient false value 0 = some (value + 1) := by
  rfl

theorem divisionPanicSkipsJoin (value : Int64) :
    IncrementWithOptionalQuotient true value 0 = none := by
  rfl
