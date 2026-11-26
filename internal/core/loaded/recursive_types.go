package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type RecursiveEdge struct {
	Target uint
	Direct bool
}

type RecursiveTypeNode struct {
	Edges         lean.Array[RecursiveEdge]
	Enum, SelfBox bool
}

type RecursiveTypeProblem uint8

const (
	ValidRecursiveTypes RecursiveTypeProblem = iota
	UnsupportedRecursiveEdge
	UnsupportedRecursiveRecord
)

type RecursiveTypeCheck struct {
	Problem        RecursiveTypeProblem
	Source, Target uint
}

type componentMembership struct {
	Groups     lean.Array[lean.Array[uint]]
	Membership lean.OrderedMap[uint, uint]
}

type memberGroup struct {
	Members    lean.Array[uint]
	Group      uint
	Membership lean.OrderedMap[uint, uint]
}

func indexGroupMember(index uint, state memberGroup) memberGroup {
	member := state.Members.Get(index).UnwrapOr(0)
	return memberGroup{Members: state.Members, Group: state.Group, Membership: state.Membership.Insert(member, state.Group)}
}

func indexGroup(index uint, state componentMembership) componentMembership {
	members := state.Groups.Get(index).UnwrapOr(lean.Array[uint]{})
	initial := memberGroup{Members: members, Group: index, Membership: state.Membership}
	result := lean.FoldN(members.Size(), initial, indexGroupMember)
	return componentMembership{Groups: state.Groups, Membership: result.Membership}
}

type cyclicEdgeCheck struct {
	Membership    lean.OrderedMap[uint, uint]
	Edges         lean.Array[RecursiveEdge]
	Group, Source uint
	Recursive     bool
	Check         RecursiveTypeCheck
}

func stepCyclicEdge(index uint, state cyclicEdgeCheck) lean.FoldControl[cyclicEdgeCheck] {
	edge := state.Edges.Get(index).UnwrapOr(RecursiveEdge{Target: 0, Direct: true})
	member := state.Membership.Find(edge.Target)
	if !member.IsSome() || member.UnwrapOr(0) != state.Group {
		return lean.FoldControl[cyclicEdgeCheck]{State: state, Stop: false}
	}
	check := validateCyclicEdge(state.Source, edge)
	next := cyclicEdgeCheck{Membership: state.Membership, Edges: state.Edges, Group: state.Group,
		Source: state.Source, Recursive: true, Check: check}
	return lean.FoldControl[cyclicEdgeCheck]{State: next, Stop: check.Problem != ValidRecursiveTypes}
}

func validRecursiveTypes() RecursiveTypeCheck {
	return RecursiveTypeCheck{Problem: ValidRecursiveTypes, Source: 0, Target: 0}
}

func validateCyclicEdge(source uint, edge RecursiveEdge) RecursiveTypeCheck {
	if !edge.Direct {
		return RecursiveTypeCheck{Problem: UnsupportedRecursiveEdge, Source: source, Target: edge.Target}
	}
	return validRecursiveTypes()
}

type recursiveMembers struct {
	Nodes              lean.Array[RecursiveTypeNode]
	Members            lean.Array[uint]
	Membership         lean.OrderedMap[uint, uint]
	Group              uint
	HasEnum, Recursive bool
	Check              RecursiveTypeCheck
}

func checkRecursiveMember(index uint, state recursiveMembers) lean.FoldControl[recursiveMembers] {
	source := state.Members.Get(index).UnwrapOr(0)
	node := recursiveNodeAt(state.Nodes, source)
	initial := cyclicEdgeCheck{Membership: state.Membership, Edges: node.Edges, Group: state.Group,
		Source: source, Recursive: state.Recursive, Check: validRecursiveTypes()}
	result := lean.FoldNUntil(node.Edges.Size(), initial, stepCyclicEdge)
	next := recursiveMembers{Nodes: state.Nodes, Members: state.Members, Membership: state.Membership,
		Group: state.Group, HasEnum: state.HasEnum || node.Enum, Recursive: result.State.Recursive, Check: result.State.Check}
	return lean.FoldControl[recursiveMembers]{State: next, Stop: result.Stop}
}

func recursiveNodeAt(nodes lean.Array[RecursiveTypeNode], index uint) RecursiveTypeNode {
	return nodes.Get(index).UnwrapOr(RecursiveTypeNode{Edges: lean.Array[RecursiveEdge]{}, Enum: false, SelfBox: false})
}

type recursiveGroups struct {
	Nodes      lean.Array[RecursiveTypeNode]
	Membership componentMembership
	Check      RecursiveTypeCheck
}

func checkRecursiveGroup(index uint, state recursiveGroups) lean.FoldControl[recursiveGroups] {
	group := state.Membership.Groups.Get(index).UnwrapOr(lean.Array[uint]{})
	initial := recursiveMembers{Nodes: state.Nodes, Members: group, Membership: state.Membership.Membership,
		Group: index, HasEnum: false, Recursive: group.Size() > 1, Check: validRecursiveTypes()}
	checked := lean.FoldNUntil(group.Size(), initial, checkRecursiveMember)
	result := finishRecursiveGroup(checked.State)
	next := recursiveGroups{Nodes: state.Nodes, Membership: state.Membership, Check: result}
	return lean.FoldControl[recursiveGroups]{State: next, Stop: result.Problem != ValidRecursiveTypes}
}

func finishRecursiveGroup(state recursiveMembers) RecursiveTypeCheck {
	if state.Check.Problem != ValidRecursiveTypes {
		return state.Check
	}
	if state.Recursive && !state.HasEnum {
		first := state.Members.Get(0).UnwrapOr(0)
		if state.Members.Size() != 1 || !recursiveNodeAt(state.Nodes, first).SelfBox {
			return RecursiveTypeCheck{Problem: UnsupportedRecursiveRecord, Source: first, Target: 0}
		}
	}
	return state.Check
}

// CheckRecursiveTypes checks components in completion order. Within a
// component, container restrictions take precedence over the record rule.
//
//golean:export
func CheckRecursiveTypes(nodes lean.Array[RecursiveTypeNode], components Components) RecursiveTypeCheck {
	initial := componentMembership{Groups: components.Groups, Membership: lean.OrderedMap[uint, uint]{}}
	membership := lean.FoldN(components.Groups.Size(), initial, indexGroup)
	checking := recursiveGroups{Nodes: nodes, Membership: membership, Check: validRecursiveTypes()}
	return lean.FoldNUntil(components.Groups.Size(), checking, checkRecursiveGroup).State.Check
}
