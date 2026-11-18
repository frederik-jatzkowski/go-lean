import byte_rune.byte_rune_gen
import Std.Tactic.BVDecide

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/byte_rune».byte_rune

theorem lowerASCIIIdempotent (b : UInt8) : LowerASCII (LowerASCII b) = LowerASCII b := by
  unfold LowerASCII
  simp only [show UInt8.ofNat 65 = (65 : UInt8) from rfl,
    show UInt8.ofNat 90 = (90 : UInt8) from rfl,
    show UInt8.ofNat 32 = (32 : UInt8) from rfl]
  bv_decide

theorem asciiDigit : DigitValue 0x39 = 9 := by
  decide

theorem nonASCIIDigit : DigitValue 0x660 = -1 := by
  decide
