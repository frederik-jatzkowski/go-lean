import boolean_implication.boolean_implication_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/boolean_implication».boolean_implication

theorem impliesFalse (q : Bool) : Implies false q = true := by
  rfl

theorem impliesTrue (q : Bool) : Implies true q = q := by
  rfl

theorem falseSkipsDivision (x : Int64) : AndCheck false x 0 = some false := by
  rfl

theorem trueEvaluatesDivision (x : Int64) : AndCheck true x 0 = none := by
  rfl
