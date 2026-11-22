import arithmetic.arithmetic_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/arithmetic».arithmetic.Proofs

theorem cancelAdd : Laws.cancelAdd := by
  intro x y
  simp [CancelAdd]

theorem multiplyByOne : Laws.multiplyByOne := by
  intro x
  simp [MultiplyByOne]

theorem incrementWraps : Laws.incrementWraps := by
  unfold Laws.incrementWraps
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/arithmetic».arithmetic.Proofs
