import boolean_implication.boolean_implication_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/boolean_implication».boolean_implication.Proofs

theorem impliesFalse : Laws.impliesFalse := by
  intro q
  rfl

theorem impliesTrue : Laws.impliesTrue := by
  intro q
  rfl

theorem falseSkipsDivision : Laws.falseSkipsDivision := by
  intro x
  rfl

theorem trueEvaluatesDivision : Laws.trueEvaluatesDivision := by
  intro x
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/boolean_implication».boolean_implication.Proofs
