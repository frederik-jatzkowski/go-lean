import struct_fields.struct_fields_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/struct_fields».struct_fields.Proofs

theorem swapInvolutive : Laws.swapInvolutive := by
  intro point
  cases point <;> rfl

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/struct_fields».struct_fields.Proofs
