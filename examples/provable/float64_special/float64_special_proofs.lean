import float64_special.float64_special_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/float64_special».float64_special
open Float.Model (UnpackedFloat)

private theorem unpackedUnequalToSelf (x : UnpackedFloat) : (!x.beq x) = x.isNaN := by
  cases x with
  | notANumber => rfl
  | zero _ => rfl
  | infinity sign => cases sign <;> rfl
  | finite sign _ _ _ =>
    cases sign <;> simp [UnpackedFloat.beq, UnpackedFloat.compare, UnpackedFloat.isNaN]

theorem detectsNaN (x : Float) : IsNaN x = x.isNaN :=
  unpackedUnequalToSelf x.toModel.unpack

private theorem unpackedNaNIsUnordered (x y : UnpackedFloat)
    (h : x.isNaN = true ∨ y.isNaN = true) : x.lt y = false := by
  cases x <;> cases y <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isNaN] at *

theorem nanIsUnordered (x y : Float) (h : x.isNaN = true ∨ y.isNaN = true) :
    Less x y = false :=
  unpackedNaNIsUnordered x.toModel.unpack y.toModel.unpack h

theorem signedZeroEqualsZero : IsZero (Float.ofBits 0x8000000000000000) = true := by
  decide

theorem nanDoesNotEqualZero : IsZero (Float.ofBits 0x7ff8000000000000) = false := by
  decide

theorem preservesSubnormalConstant : SmallestPositive.toBits = 1 := by
  decide
