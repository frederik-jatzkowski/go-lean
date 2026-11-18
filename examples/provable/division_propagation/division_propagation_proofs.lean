import division_propagation.division_propagation_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_propagation».division_propagation

theorem propagatesDivisionPanic (x : Int64) : DivideThenIncrement x 0 = none := by
  simp [DivideThenIncrement, quotient]

theorem incrementsSuccessfulQuotient (x divisor : Int64) (h : divisor ≠ 0) :
    DivideThenIncrement x divisor = some (Int64.ofInt (x.toInt.tdiv divisor.toInt) + 1) := by
  simp [DivideThenIncrement, quotient, h]
