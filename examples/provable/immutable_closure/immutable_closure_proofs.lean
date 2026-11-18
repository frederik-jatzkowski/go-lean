-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import immutable_closure.immutable_closure_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/immutable_closure».immutable_closure

theorem capturedOffsetIsAdded (value offset : Int64) :
    AddOffset value offset = value + offset := by
  sorry
