import machine_words.machine_words_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/machine_words».machine_words.Proofs

theorem roundTrip : Laws.roundTrip := by
  intro x
  rfl

theorem negativeOneUsesAllBits : Laws.negativeOneUsesAllBits := by
  unfold Laws.negativeOneUsesAllBits
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/machine_words».machine_words.Proofs
