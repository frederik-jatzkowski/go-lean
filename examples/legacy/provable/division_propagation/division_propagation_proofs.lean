import division_propagation.division_propagation_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_propagation».division_propagation.Proofs

theorem propagatesDivisionPanic : Laws.propagatesDivisionPanic := by
  intro x
  simp [DivideThenIncrement, quotient]

theorem incrementsSuccessfulQuotient : Laws.incrementsSuccessfulQuotient := by
  intro x divisor h
  simp [DivideThenIncrement, quotient, h]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/division_propagation».division_propagation.Proofs
