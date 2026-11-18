-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import machine_words.machine_words_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/machine_words».machine_words

-- ISize and USize model the Go target's machine word width.
theorem roundTrip (x : ISize) : RoundTrip x = x := by
  sorry

theorem negativeOneUsesAllBits : ToUnsigned (-1) = (0 : USize) - 1 := by
  sorry
