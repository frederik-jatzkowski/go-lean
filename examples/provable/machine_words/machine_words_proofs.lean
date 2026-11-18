import machine_words.machine_words_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/machine_words».machine_words

theorem roundTrip (x : GoTypes.Int) : RoundTrip x = x := by
  rfl

theorem negativeOneUsesAllBits : ToUnsigned (-1) = (0 : GoTypes.UInt) - 1 := by
  decide
