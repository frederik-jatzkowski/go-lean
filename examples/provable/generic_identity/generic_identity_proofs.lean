import generic_identity.generic_identity_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/generic_identity».generic_identity

theorem identityPreservesValue {α : Type} (value : α) : Identity value = value := by
  rfl
