package lean

import "testing"

func TestFoldDrivers(t *testing.T) {
	list := Cons(3, Cons(7, Cons(9, Nil[int]())))
	for _, tc := range []struct {
		name    string
		count   uint
		list    List[int]
		stop    int
		want    int
		stopped bool
	}{
		{name: "empty", stop: 0},
		{name: "first", count: 1, list: list, stop: 0, want: 3, stopped: true},
		{name: "last", count: 3, list: list, stop: 2, want: 379, stopped: true},
		{name: "exhausted", count: 3, list: list, stop: 4, want: 379},
	} {
		t.Run(tc.name, func(t *testing.T) {
			digits := [...]int{3, 7, 9}
			counted := FoldNUntil(tc.count, 0, func(i uint, state int) FoldControl[int] {
				return FoldControl[int]{State: state*10 + digits[i], Stop: i == uint(tc.stop)}
			})
			calls := 0
			walked := FoldListUntil(tc.list, 0, func(value, state int) FoldControl[int] {
				stop := calls == tc.stop
				calls++
				return FoldControl[int]{State: state*10 + value, Stop: stop}
			})
			want := FoldControl[int]{State: tc.want, Stop: tc.stopped}
			if counted != want || walked != want {
				t.Fatalf("counted %v, list %v, want %v", counted, walked, want)
			}
		})
	}
	if got := FoldN(3, 0, func(i uint, state int) int { return state*10 + int(i) + 1 }); got != 123 {
		t.Fatalf("FoldN returned %d", got)
	}
	if got := FoldList(list, 0, func(value, state int) int { return state*10 + value }); got != 379 {
		t.Fatalf("FoldList returned %d", got)
	}
}
