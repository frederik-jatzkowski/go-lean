package string_bytes

//golean:verify joinBytes : ∀ (a b : ByteArray),
//golean:verify+   (Join a b).data.toList = a.data.toList ++ b.data.toList
func Join(a, b string) string { return a + b }

//golean:verify lengthIsByteCount : ∀ (s : ByteArray) (fits : s.size < 2 ^ (GoTypes.WordBits - 1)),
//golean:verify+   (ByteLen s).toInt = Int.ofNat s.size
//golean:verify lenCountsRawBytes : ByteLen (AddRawPrefix (ByteArray.mk #[128])) = 3
func ByteLen(s string) int { return len(s) }

//golean:verify preservesRawBytes : (AddRawPrefix (ByteArray.mk #[128])).data.toList = [255, 0, 128]
func AddRawPrefix(s string) string { return "\xff\x00" + s }

//golean:verify toBytesPreservesContents : ∀ (s : ByteArray),
//golean:verify+   (ToBytes s).length = s.size ∧ ToBytes s = s.data.toList
func ToBytes(s string) []byte { return []byte(s) }
