import float64_special.float64_special_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float64_special».float64_special.Proofs
open Float.Model (UnpackedFloat)

private theorem unpackedUnequalToSelf (x : UnpackedFloat) : (!x.beq x) = x.isNaN := by
  cases x with
  | notANumber => rfl
  | zero _ => rfl
  | infinity sign => cases sign <;> rfl
  | finite sign _ _ _ =>
    cases sign <;> simp [UnpackedFloat.beq, UnpackedFloat.compare, UnpackedFloat.isNaN]

theorem detectsNaN : Laws.detectsNaN := by
  intro x
  exact unpackedUnequalToSelf x.toModel.unpack

private theorem unpackedNaNIsUnordered (x y : UnpackedFloat)
    (h : x.isNaN = true ∨ y.isNaN = true) : x.lt y = false := by
  cases x <;> cases y <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isNaN] at *

theorem nanIsUnordered : Laws.nanIsUnordered := by
  intro x y h
  exact unpackedNaNIsUnordered x.toModel.unpack y.toModel.unpack h

theorem signedZeroEqualsZero : Laws.signedZeroEqualsZero := by
  unfold Laws.signedZeroEqualsZero
  decide

theorem nanDoesNotEqualZero : Laws.nanDoesNotEqualZero := by
  unfold Laws.nanDoesNotEqualZero
  decide

theorem preservesSubnormalConstant : Laws.preservesSubnormalConstant := by
  unfold Laws.preservesSubnormalConstant
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float64_special».float64_special.Proofs
