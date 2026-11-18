-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import nil_dereference.nil_dereference_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nil_dereference».nil_dereference

theorem readNonNilPanicFree (record : Record) :
    ∃ value, Read (some record) = some value := by
  sorry

theorem readNilPanics : Read (none : Option Record) = none := by
  sorry
