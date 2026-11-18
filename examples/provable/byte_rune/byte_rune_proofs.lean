-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import byte_rune.byte_rune_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/byte_rune».byte_rune

theorem lowerASCIIIdempotent (b : UInt8) : LowerASCII (LowerASCII b) = LowerASCII b := by
  sorry

theorem asciiDigit : DigitValue 0x39 = 9 := by
  sorry

theorem nonASCIIDigit : DigitValue 0x660 = -1 := by
  sorry
