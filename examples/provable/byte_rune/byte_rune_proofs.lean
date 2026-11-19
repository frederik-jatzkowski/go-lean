import byte_rune.byte_rune_gen
import Lean.Elab.Tactic.Omega

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/byte_rune».byte_rune.Proofs

private theorem lowerASCIIModel (b : UInt8) :
    LowerASCII b = if 65 ≤ b then (if b ≤ 90 then b + 32 else b) else b := by
  simp [LowerASCII]

theorem lowerASCIIIdempotent : Laws.lowerASCIIIdempotent := by
  intro b
  by_cases low : 65 ≤ b
  · by_cases high : b ≤ 90
    · have shifted : ¬ b + 32 ≤ (90 : UInt8) := by
        simp only [UInt8.le_iff_toNat_le, UInt8.toNat_add] at low high ⊢
        simp at low high ⊢
        omega
      have once : LowerASCII b = b + 32 := by simp [lowerASCIIModel, low, high]
      calc
        LowerASCII (LowerASCII b) = LowerASCII (b + 32) := congrArg LowerASCII once
        _ = b + 32 := by simp [lowerASCIIModel, shifted]
        _ = LowerASCII b := once.symm
    · have same : LowerASCII b = b := by simp [lowerASCIIModel, low, high]
      rw [same, same]
  · have same : LowerASCII b = b := by simp [lowerASCIIModel, low]
    rw [same, same]

theorem asciiDigit : Laws.asciiDigit := by
  unfold Laws.asciiDigit
  decide

theorem nonASCIIDigit : Laws.nonASCIIDigit := by
  unfold Laws.nonASCIIDigit
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/byte_rune».byte_rune.Proofs
