package loaded

import (
	"reflect"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func testGraph(edges ...[]uint) lean.Array[GraphNode] {
	nodes := make([]GraphNode, len(edges))
	for i, targets := range edges {
		nodes[i] = GraphNode{Edges: lean.ArrayFromSlice(targets)}
	}
	return lean.ArrayFromSlice(nodes)
}

func TestStrongComponents(t *testing.T) {
	result := StrongComponents(testGraph([]uint{1}, []uint{2, 3}, []uint{0}, []uint{4}, []uint{3}, nil))
	if !result.Complete {
		t.Fatal("traversal exhausted the graph budget")
	}
	want := [][]uint{{4, 3}, {2, 1, 0}, {5}}
	var got [][]uint
	for i := range result.Groups.Size() {
		group := result.Groups.Get(i).UnwrapOr(lean.Array[uint]{})
		var members []uint
		for j := range group.Size() {
			members = append(members, group.Get(j).UnwrapOr(99))
		}
		got = append(got, members)
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestOrderDependencies(t *testing.T) {
	graph := testGraph([]uint{1, 2}, nil, []uint{1}, []uint{3})
	roots := lean.ArrayFromSlice([]uint{4, 0, 2, 4, 3})
	result := OrderDependencies(graph, roots)
	if !result.Complete {
		t.Fatal("traversal exhausted the graph budget")
	}
	want := []GraphPlacement{{RootIndex: 1, Node: 1}, {RootIndex: 1, Node: 2}, {RootIndex: 1, Node: 0}, {RootIndex: 4, Node: 3}}
	var got []GraphPlacement
	for i := range result.Placements.Size() {
		got = append(got, result.Placements.Get(i).UnwrapOr(GraphPlacement{}))
	}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestRecursiveTypeDiagnosticOrder(t *testing.T) {
	graph := testGraph([]uint{1}, []uint{0}, []uint{2})
	groups := StrongComponents(graph)
	nodes := []RecursiveTypeNode{
		{Edges: lean.ArrayFromSlice([]RecursiveEdge{{Target: 1, Direct: true}})},
		{Edges: lean.ArrayFromSlice([]RecursiveEdge{{Target: 0, Direct: false}})},
		{Edges: lean.ArrayFromSlice([]RecursiveEdge{{Target: 2, Direct: false}})},
	}
	check := CheckRecursiveTypes(lean.ArrayFromSlice(nodes), groups)
	if check != (RecursiveTypeCheck{Problem: UnsupportedRecursiveEdge, Source: 1, Target: 0}) {
		t.Fatalf("expected the first component's unsupported edge, got %+v", check)
	}
	nodes[1].Edges = lean.ArrayFromSlice([]RecursiveEdge{{Target: 0, Direct: true}})
	check = CheckRecursiveTypes(lean.ArrayFromSlice(nodes), groups)
	if check != (RecursiveTypeCheck{Problem: UnsupportedRecursiveRecord, Source: 1}) {
		t.Fatalf("expected the first component's recursive record, got %+v", check)
	}
}
