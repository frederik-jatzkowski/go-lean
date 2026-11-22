package multiresult

//golean:export
func Divide(x, d int64) (input int64, quotient int64, negative bool) {
	input = x
	quotient = x / d
	if quotient < 0 {
		negative = true
	}
	return
}

func order(input, quotient int64, negative bool) (bool, int64, int64) {
	return negative, quotient, input
}

//golean:verify reordersAllResults : Reorder (-12) 3 = some (true, (-4, -12))
//golean:verify laterResultPanicAbortsCall : ∀ (x : Int64),
//golean:verify+   Reorder x 0 = none ∧ First x 0 = none ∧ Discard x 0 = none
func Reorder(x, d int64) (bool, int64, int64) {
	return order(Divide(x, d))
}

//golean:export
func Discard(x, d int64) bool {
	Divide(x, d)
	return true
}

//golean:export
func First(x, d int64) int64 {
	input, _, _ := Divide(x, d)
	return input
}

type Counter struct {
	Value int64
}

//golean:verify concreteReceiverResults : «Counter$Read» ⟨-3⟩ = (-3, true) ∧
//golean:verify+ «Counter$Peek» (some ⟨4⟩) = some (4, false) ∧
//golean:verify+ «Counter$Peek» none = none
func (c Counter) Read() (int64, bool) {
	return c.Value, c.Value < 0
}

//golean:export
func (c *Counter) Peek() (int64, bool) {
	return c.Value, c.Value < 0
}

func (c *Counter) add(amount int64) (int64, int64) {
	before := c.Value
	c.Value += amount
	return before, c.Value
}

//golean:verify statefulCallsThreadReceiver : «Counter$AddTwice» (some ⟨3⟩) 2 = some (some ⟨7⟩, (3, 7))
func (c *Counter) AddTwice(amount int64) (int64, int64) {
	before, _ := c.add(amount)
	_, after := c.add(amount)
	return before, after
}

//golean:verify loopAndRecursiveResults : Count 4 = (4, 8) ∧ Fold [7, -1, 2] = (3, 8) ∧ Chain [7, -1, 2] = (3, 8)
func Count(n int) (int64, int64) {
	var count, total int64
	for i := 0; i < n; i++ {
		count++
		total += 2
	}
	return count, total
}

//golean:export
func Fold(xs []int64) (int64, int64) {
	var count, total int64
	for _, x := range xs {
		count++
		total += x
	}
	return count, total
}

type Node struct {
	Value int64
	Next  *Node
}

//golean:export
func Chain(node *Node) (int64, int64) {
	if node == nil {
		return 0, 0
	}
	count, total := Chain(node.Next)
	return count + 1, total + node.Value
}

//golean:export
func Maps(k int64) (map[int64]int64, bool, map[int64]int64) {
	first := make(map[int64]int64)
	second := make(map[int64]int64)
	first[k] = 1
	second[k] = 2
	_, ok := first[k]
	return first, ok, second
}

//golean:export
func Copy(xs []int64) ([]int64, int) {
	dst := make([]int64, len(xs))
	n := copy(dst, xs)
	return dst, n
}

//golean:export
func Double(xs []int64) (int, []int64) {
	dst := make([]int64, len(xs))
	for i, x := range xs {
		dst[i] = x + x
	}
	return len(xs), dst
}

//golean:verify freshSliceResults : ForwardSlice [3, 5] = some ([3, 5], 2) ∧ Double [3, 5] = some (2, [6, 10])
func ForwardSlice(xs []int64) ([]int64, int) {
	return Copy(xs)
}

//golean:verify distinctFreshMaps : ForwardMaps 5 = some ([(5, 1)], (true, [(5, 2)]))
func ForwardMaps(key int64) (map[int64]int64, bool, map[int64]int64) {
	return Maps(key)
}

//golean:verify effectfulSliceResults : Reciprocals [3, 6] = some ([4, 2], 2) ∧ Reciprocals [3, 0] = none
func Reciprocals(xs []int64) ([]int64, int) {
	dst := make([]int64, len(xs))
	for i, x := range xs {
		dst[i] = 12 / x
	}
	return dst, len(xs)
}

type Queue struct {
	Cursor int
	Values []int64
	Total  int64
}

//golean:verify statefulLoopResults : «Queue$Drain» (some ⟨0, some [3, 6], 1⟩) =
//golean:verify+ some (some ⟨2, some [3, 6], 10⟩, (10, 2))
func (q *Queue) Drain() (int64, int) {
	for q.Cursor < len(q.Values) {
		q.Total += q.Values[q.Cursor]
		q.Cursor++
	}
	return q.Total, q.Cursor
}
