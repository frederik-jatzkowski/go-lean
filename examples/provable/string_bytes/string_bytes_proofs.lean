import string_bytes.string_bytes_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_bytes».string_bytes

-- Go strings are byte sequences and can contain invalid UTF-8.
theorem joinBytes (a b : ByteArray) :
    (Join a b).data.toList = a.data.toList ++ b.data.toList := by
  simp [Join]

theorem lengthIsByteCount (s : ByteArray) (fits : s.size < 2 ^ (GoTypes.WordBits - 1)) :
    (ByteLen s).toInt = Int.ofNat s.size := by
  unfold ByteLen
  first
  | exact Int64.toInt_ofNat_of_lt fits
  | exact Int32.toInt_ofNat_of_lt fits

theorem preservesRawBytes :
    (AddRawPrefix (ByteArray.mk #[128])).data.toList = [255, 0, 128] := by
  decide

theorem lenCountsRawBytes : ByteLen (AddRawPrefix (ByteArray.mk #[128])) = 3 := by
  decide
