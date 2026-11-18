import slice_copy.slice_copy_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/slice_copy».slice_copy

-- The theorem specifies the copy's contents. The Go implementation allocates fresh storage.
theorem clonePreservesContents (xs : List Int64) : Clone xs = some xs := by
  simp [Clone]
