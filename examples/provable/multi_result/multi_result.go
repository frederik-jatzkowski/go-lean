package multiresult

//golean:verify
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

//golean:verify
func Reorder(x, d int64) (bool, int64, int64) {
	return order(Divide(x, d))
}

//golean:verify
func Discard(x, d int64) bool {
	Divide(x, d)
	return true
}

//golean:verify
func First(x, d int64) int64 {
	input, _, _ := Divide(x, d)
	return input
}

type Counter struct {
	Value int64
}

//golean:verify
func (c Counter) Read() (int64, bool) {
	return c.Value, c.Value < 0
}

//golean:verify
func (c *Counter) Peek() (int64, bool) {
	return c.Value, c.Value < 0
}

func (c *Counter) add(amount int64) (int64, int64) {
	before := c.Value
	c.Value += amount
	return before, c.Value
}

//golean:verify
func (c *Counter) AddTwice(amount int64) (int64, int64) {
	before, _ := c.add(amount)
	_, after := c.add(amount)
	return before, after
}

//golean:verify
func Count(n int) (int64, int64) {
	var count, total int64
	for i := 0; i < n; i++ {
		count++
		total += 2
	}
	return count, total
}

//golean:verify
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

//golean:verify
func Chain(node *Node) (int64, int64) {
	if node == nil {
		return 0, 0
	}
	count, total := Chain(node.Next)
	return count + 1, total + node.Value
}

//golean:verify
func Maps(k int64) (map[int64]int64, bool, map[int64]int64) {
	first := make(map[int64]int64)
	second := make(map[int64]int64)
	first[k] = 1
	second[k] = 2
	_, ok := first[k]
	return first, ok, second
}

//golean:verify
func Copy(xs []int64) ([]int64, int) {
	dst := make([]int64, len(xs))
	n := copy(dst, xs)
	return dst, n
}

//golean:verify
func Double(xs []int64) (int, []int64) {
	dst := make([]int64, len(xs))
	for i, x := range xs {
		dst[i] = x + x
	}
	return len(xs), dst
}

//golean:verify
func ForwardSlice(xs []int64) ([]int64, int) {
	return Copy(xs)
}

//golean:verify
func ForwardMaps(key int64) (map[int64]int64, bool, map[int64]int64) {
	return Maps(key)
}

//golean:verify
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

//golean:verify
func (q *Queue) Drain() (int64, int) {
	for q.Cursor < len(q.Values) {
		q.Total += q.Values[q.Cursor]
		q.Cursor++
	}
	return q.Total, q.Cursor
}
