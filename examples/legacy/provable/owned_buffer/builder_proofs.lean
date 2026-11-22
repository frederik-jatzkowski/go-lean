import owned_buffer.builder_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/owned_buffer»

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/owned_buffer».builder.Proofs

theorem appendReturnsIndex : Laws.appendReturnsIndex := by
  intro before inst
  exact ⟨rfl, Array.getElem?_push_size⟩

theorem patchPreservesOffsets : Laws.patchPreservesOffsets := by
  intro before index target old nonnegative found
  let code := before.«field:code».getD #[]
  let patched := { old with «field:Target» := target }
  have bound : index.toNatClampNeg < code.size :=
    (getElem?_eq_some_iff.mp found).choose
  refine ⟨{ before with «field:code» := some (code.setIfInBounds index.toNatClampNeg patched) }, ?_, rfl, ?_⟩
  · simp [«Builder$patch», Int.not_lt.mpr nonnegative, found, code, patched]
  · exact Array.getElem?_setIfInBounds_self_of_lt bound

theorem buildsThree : Laws.buildsThree := by
  unfold Laws.buildsThree
  decide +kernel

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/owned_buffer».builder.Proofs
