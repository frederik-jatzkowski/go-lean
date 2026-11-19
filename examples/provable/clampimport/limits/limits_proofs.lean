import clampimport.limits.limits_gen
import Lean.Elab.Tactic.Omega

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clampimport/limits».limits.Proofs

theorem atMostRight : Laws.atMostRight := by
  intro x y
  simp only [Min, decide_eq_true_eq]
  split <;> simp_all only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt] <;> omega

theorem leftIdentity : Laws.leftIdentity := by
  intro x y ordered
  simp only [Min, decide_eq_true_eq]
  split <;> simp_all only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] <;> omega

theorem rightIdentity : Laws.rightIdentity := by
  intro x y ordered
  simp only [Min, decide_eq_true_eq]
  split <;> simp_all only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] <;> omega

theorem atLeastRight : Laws.atLeastRight := by
  intro x y
  simp only [Max, decide_eq_true_eq]
  split <;> simp_all only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt] <;> omega

theorem leftIdentityMax : Laws.leftIdentityMax := by
  intro x y ordered
  simp only [Max, decide_eq_true_eq]
  split <;> simp_all only [Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] <;> omega

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/clampimport/limits».limits.Proofs
