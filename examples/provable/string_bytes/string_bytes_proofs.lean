-- Pending proof draft. The imported definitions will be generated when this feature is supported.
import string_bytes.string_bytes_gen

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/string_bytes».string_bytes

-- Go strings are byte sequences and can contain invalid UTF-8.
theorem joinBytes (a b : ByteArray) :
    (Join a b).data.toList = a.data.toList ++ b.data.toList := by
  sorry

theorem lengthIsByteCount (s : ByteArray) (fits : s.size < 2 ^ (System.Platform.numBits - 1)) :
    (ByteLen s).toInt = Int.ofNat s.size := by
  sorry
