-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import boolean_implication.boolean_implication_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/boolean_implication».boolean_implication

theorem impliesFalse (q : Bool) : Implies false q = true := by
  sorry

theorem impliesTrue (q : Bool) : Implies true q = q := by
  sorry
