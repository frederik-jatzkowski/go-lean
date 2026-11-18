import embedded_struct.embedded_struct_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/embedded_struct».embedded_struct

theorem promotionReadsEmbeddedField (sample : Sample) :
    PromotedX sample = ExplicitX sample := by
  rfl
