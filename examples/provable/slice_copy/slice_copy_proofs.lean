import slice_copy.slice_copy_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_copy».slice_copy.Proofs

-- The theorem specifies the copy's contents. The Go implementation allocates fresh storage.
theorem clonePreservesContents : Laws.clonePreservesContents := by
  intro xs
  simp [Clone]

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_copy».slice_copy.Proofs
