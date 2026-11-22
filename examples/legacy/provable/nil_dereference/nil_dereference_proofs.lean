import nil_dereference.nil_dereference_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nil_dereference».nil_dereference.Proofs

theorem readNonNilPanicFree : Laws.readNonNilPanicFree := by
  intro record
  exact ⟨record.«field:Value», rfl⟩

theorem readNilPanics : Laws.readNilPanics := by
  rfl

theorem readReturnsField : Laws.readReturnsField := by
  intro record
  rfl

theorem takingNilFieldAddressPanics : Laws.takingNilFieldAddressPanics := by
  rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/nil_dereference».nil_dereference.Proofs
