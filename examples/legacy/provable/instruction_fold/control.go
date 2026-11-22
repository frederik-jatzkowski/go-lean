package instruction_fold

//golean:verify controlPaths : firstAbove [-1, 2, 3, 9] 1 = some 3 ∧
//golean:verify+   firstAbove [2, 3, 9] 3 = some 3 ∧
//golean:verify+   firstAbove [-1, 1, 2] 9 = some 4
func firstAbove(values []int64, limit int64) int64 {
	var sum int64
	for _, value := range values {
		switch {
		case value < 0:
			continue
		case value == limit:
			return value
		}
		if sum > limit {
			break
		}
		sum += value
	}
	return sum + 1
}

//golean:verify arraySnapshot : snapshotRange #v[1, 2, 3] #v[7, 8, 9] = some 10
func snapshotRange(values, replacement [3]int64) int64 {
	for i, value := range values {
		values = replacement
		if i == 1 {
			return value + second(values)
		}
	}
	return 0
}

func second(values [3]int64) int64 {
	return values[1]
}

func divide(value, divisor int64) int64 {
	return value / divisor
}

//golean:verify loopCallPropagatesPanic : divideRepeated 0 8 0 = some 8 ∧
//golean:verify+   divideRepeated 1 8 0 = none ∧ divideRepeated 2 8 2 = some 2
func divideRepeated(count uint8, value, divisor int64) int64 {
	for i := uint8(0); i < count; i++ {
		value = divide(value, divisor)
	}
	return value
}

//golean:verify checkedLoopIndex : sumPrefix [0, 0] [3, 4] = some 7 ∧
//golean:verify+   sumPrefix [0, 0] [3] = none ∧ sumPrefix [] [] = some 0
func sumPrefix(bounds, values []int64) int64 {
	var sum int64
	for i := 0; i < len(bounds); i++ {
		sum += values[i]
	}
	return sum
}
