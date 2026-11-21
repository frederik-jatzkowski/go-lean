package owned_collection

//golean:verify conditionalWrites : ∀ (length : Int64) (keep : Bool),
//golean:verify+   Build length keep = some (if length = 2 then [if keep then 7 else 0, 0] else [])
func Build(length int64, keep bool) []int64 {
	if length != 2 {
		length = 0
	}
	buf := make([]int64, length)
	for i := int64(0); i < length; i++ {
		if keep && i == 0 {
			buf[i] = 7
		}
	}
	return buf
}

//golean:verify checkedWrite : Write 2 1 = some [0, 7] ∧ Write 2 2 = none ∧ Write 2 (-1) = none
func Write(length int64, index int64) []int64 {
	buf := make([]int64, length)
	buf[index] = 7
	return buf
}

//golean:verify repeatedMapUpdates : Count [3, 3, 3] = some [(3, 3)] ∧ Count [] = some []
func Count(keys []int64) map[int64]int64 {
	counts := make(map[int64]int64)
	for _, key := range keys {
		counts[key] = counts[key] + 1
	}
	return counts
}

//golean:verify appendsConsumeView : AppendSelected 4 = [0, 1, 9] ∧ AppendSelected 0 = []
func AppendSelected(limit int64) []int64 {
	out := make([]int64, 0)
	for i := int64(0); i < limit; i++ {
		if i < 2 {
			out = append(out, i)
			if i == 1 {
				out = append(out, 9)
			}
		}
	}
	return out
}

//golean:verify fixedSizeBuild : FixedSize true = some [0, 8] ∧ FixedSize false = some [0, 0]
func FixedSize(keep bool) []int64 {
	out := make([]int64, 2)
	if keep {
		out[1] = 8
	}
	return out
}
