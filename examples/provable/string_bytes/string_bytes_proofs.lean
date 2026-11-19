import string_bytes.string_bytes_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_bytes».string_bytes.Proofs

-- Go strings are byte sequences and can contain invalid UTF-8.
theorem joinBytes : Laws.joinBytes := by
  intro a b
  simp [Join]

theorem lengthIsByteCount : Laws.lengthIsByteCount := by
  intro s fits
  unfold ByteLen
  first
  | exact Int64.toInt_ofNat_of_lt fits
  | exact Int32.toInt_ofNat_of_lt fits

theorem preservesRawBytes : Laws.preservesRawBytes := by
  unfold Laws.preservesRawBytes
  decide

theorem lenCountsRawBytes : Laws.lenCountsRawBytes := by
  unfold Laws.lenCountsRawBytes
  decide

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_bytes».string_bytes.Proofs
