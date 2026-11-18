-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import struct_fields.struct_fields_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/struct_fields».struct_fields

theorem swapInvolutive (point : Point) : Swap (Swap point) = point := by
  sorry
