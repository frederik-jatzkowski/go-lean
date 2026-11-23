package lean

import "testing"

func check[T comparable](t *testing.T, got, want T) {
	t.Helper()
	if got != want {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestOptionAndList(t *testing.T) {
	check(t, Option[int]{}, None[int]())
	check(t, None[int]().IsSome(), false)
	check(t, None[int]().UnwrapOr(7), 7)
	check(t, Some(0).IsSome(), true)
	check(t, Some(0).UnwrapOr(7), 0)

	empty := Nil[int]()
	tail := Cons(1, empty)
	left, right := Cons(2, tail), Cons(3, tail)
	check(t, List[int]{}.IsEmpty(), true)
	check(t, empty.IsEmpty(), true)
	check(t, left.IsEmpty(), false)
	check(t, left.node.head, 2)
	check(t, right.node.head, 3)
	check(t, left.node.tail.node, tail.node)
	check(t, right.node.tail.node, tail.node)
	check(t, tail.node.head, 1)
	check(t, tail.node.tail.IsEmpty(), true)
}

func TestArray(t *testing.T) {
	var empty Array[int]
	check(t, empty.Pop().Size(), uint(0))
	check(t, empty.Set(0, 7).Size(), uint(0))
	a := empty.Push(1).Push(2)
	popped := a.Pop()
	changed := popped.Push(9).Set(0, 8)
	check(t, empty.Size(), uint(0))
	check(t, a.Size(), uint(2))
	check(t, a.Get(0), Some(1))
	check(t, a.Get(1), Some(2))
	check(t, popped.Size(), uint(1))
	check(t, popped.Get(0), Some(1))
	check(t, popped.Get(1), None[int]())
	check(t, changed.Get(0), Some(8))
	check(t, changed.Get(1), Some(9))
	check(t, a.Get(^uint(0)), None[int]())
	check(t, a.Set(^uint(0), 7).Get(1), Some(2))
}

func TestByteArray(t *testing.T) {
	var empty ByteArray
	check(t, empty.Size(), uint(0))
	check(t, empty.Get(0), None[byte]())
	check(t, empty.Push(42).Get(0), Some(byte(42)))
	source := []byte{1, 2, 3}
	a := ByteArrayFromBytes(source)
	source[1] = 9
	view := a.Extract(1, 2)
	pushed := view.Push(8)
	changed := view.Set(0, 7)
	check(t, a.Get(1), Some(byte(2)))
	check(t, a.Get(2), Some(byte(3)))
	check(t, view.Size(), uint(1))
	check(t, view.Get(0), Some(byte(2)))
	check(t, pushed.Get(1), Some(byte(8)))
	check(t, changed.Get(0), Some(byte(7)))
	check(t, a.Set(3, 6).Size(), uint(3))
	check(t, a.Extract(1, ^uint(0)).Size(), uint(2))
	check(t, a.Extract(2, 1).Size(), uint(0))
	check(t, a.Extract(2, 2).Size(), uint(0))
	check(t, a.Extract(^uint(0), ^uint(0)).Size(), uint(0))
}

func TestOrderedCollections(t *testing.T) {
	type key int
	var empty RBMap[key, string]
	check(t, empty.Find(0), None[string]())
	m := empty.Insert(2, "two").Insert(-1, "").Insert(1, "one").Insert(3, "three")
	check(t, empty.Contains(2), false)
	check(t, m.Find(-1), Some(""))
	for i, want := range []key{-1, 1, 2, 3} {
		check(t, m.entries[i].key, want)
	}
	replaced := m.Insert(2, "new")
	erased := replaced.Erase(1).Erase(99)
	check(t, m.Find(2), Some("two"))
	check(t, replaced.Find(2), Some("new"))
	check(t, replaced.Contains(1), true)
	check(t, erased.Find(1), None[string]())
	check(t, erased.Find(3), Some("three"))
	check(t, len(erased.entries), 3)

	var emptySet RBSet[string]
	s := emptySet.Insert("b").Insert("a").Insert("b")
	check(t, emptySet.Contains("b"), false)
	check(t, len(s.keys.entries), 2)
	removed := s.Erase("b").Erase("absent")
	check(t, s.Contains("b"), true)
	check(t, removed.Contains("b"), false)
	check(t, removed.Contains("a"), true)
}

func TestBitVec(t *testing.T) {
	var empty BitVec
	check(t, empty.Width(), uint(0))
	check(t, empty.Get(0), None[bool]())
	check(t, NewBitVec(65, 0), None[BitVec]())
	max := ^uint64(0)
	for _, test := range []struct {
		width uint
		value uint64
	}{
		{0, 0},
		{1, 1},
		{63, max >> 1},
		{64, max},
	} {
		option := NewBitVec(test.width, max)
		check(t, option.IsSome(), true)
		bits := option.UnwrapOr(empty)
		check(t, bits.Width(), test.width)
		check(t, bits.ToUint64(), test.value)
		check(t, bits.Get(test.width), None[bool]())
		check(t, bits.Set(test.width, true), bits)
		if test.width > 0 {
			index := test.width - 1
			cleared := bits.Set(index, false)
			check(t, cleared.Get(index), Some(false))
			check(t, bits.Get(index), Some(true))
			check(t, cleared.Set(index, true), bits)
		}
	}
	lowBit := NewBitVec(64, 1).UnwrapOr(empty)
	check(t, lowBit.Get(0), Some(true))
	check(t, lowBit.Get(63), Some(false))
}

func TestBoxCopiesValues(t *testing.T) {
	type node struct {
		value byte
		child Box[node]
	}

	input := node{value: 12}
	box := NewBox(input)
	input.value = 0
	got := box.Get()
	check(t, got.value, byte(12))
	got.value = 1
	check(t, box.Get().value, byte(12))

	var empty Box[node]
	check(t, empty.IsSome(), false)
	check(t, empty.Get().value, byte(0))
	check(t, empty.Get().child.IsSome(), false)
	check(t, NewBox(empty.Get()).IsSome(), true)
}
