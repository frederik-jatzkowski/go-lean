//go:build golean_planned

package acyclic_list

type Node struct {
	Value int64
	Next  *Node
}

// Length requires a finite, acyclic chain. Each call follows one link toward nil.
//
//golean:verify
func Length(node *Node) int64 {
	if node == nil {
		return 0
	}
	return 1 + Length(node.Next)
}
