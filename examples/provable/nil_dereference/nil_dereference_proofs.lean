import nil_dereference.nil_dereference_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nil_dereference».nil_dereference

theorem readNonNilPanicFree (record : Record) :
    ∃ value, Read (some record) = some value := by
  exact ⟨record.«field:Value», rfl⟩

theorem readNilPanics : Read (none : Option Record) = none := by
  rfl

theorem readReturnsField (record : Record) :
    Read (some record) = some record.«field:Value» := by
  rfl

theorem takingNilFieldAddressPanics : Touch (none : Option Record) = none := by
  rfl
