package movementarrival

import (
	"slices"
	"testing"
)

func TestStopsAtFirstFutureStep(t *testing.T) {
	route := []Step{{1, 0}, {2, 1}, {3, 2}}
	movement := Movement{tileID: 1, route: slices.Clone(route)}
	var queries []int
	blocked := movement.Arrive(1, func(tile int) bool {
		queries = append(queries, tile)
		return true
	})
	if blocked || movement.tileID != 2 || movement.nextStep != 2 ||
		!slices.Equal(movement.route, route) || !slices.Equal(queries, []int{2}) {
		t.Fatalf("blocked=%v movement=%+v queries=%v", blocked, movement, queries)
	}
}

func TestObstructionAfterProgressClearsRoute(t *testing.T) {
	movement := Movement{
		tileID: 2, route: []Step{{1, 0}, {4, 1}, {5, 1}, {4, 1}}, nextStep: 1,
	}
	var queries []int
	blocked := movement.Arrive(1, func(tile int) bool {
		queries = append(queries, tile)
		return len(queries) <= 2
	})
	if !blocked || movement.tileID != 5 || movement.nextStep != 0 || movement.route != nil ||
		!slices.Equal(queries, []int{4, 5, 4}) {
		t.Fatalf("blocked=%v movement=%+v queries=%v", blocked, movement, queries)
	}
}
