package generic_map

func mapValues[T, U any](values []T, transform func(T) U) []U {
	result := make([]U, len(values))
	for i, value := range values {
		result[i] = transform(value)
	}
	return result
}

//golean:verify incrementAllIsMap : ∀ (xs : List Int64),
//golean:verify+   IncrementAll xs = some (xs.map (fun x => x + 1))
func IncrementAll(values []int64) []int64 {
	return mapValues(values, func(value int64) int64 { return value + 1 })
}

//golean:export
func Nonzero(values []int64) []bool {
	return mapValues(values, func(value int64) bool { return value != 0 })
}
