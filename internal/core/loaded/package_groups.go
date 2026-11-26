package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type PackageGroups struct {
	Declarations lean.Array[CheckedDeclaration]
	Problem      RecursiveTypeProblem
	Complete     bool
	From, To     ObjectID
}

func emptyCheckedDeclaration() CheckedDeclaration {
	return CheckedDeclaration{Kind: 0, Object: 0, Type: noCheckedType(), Group: lean.Array[ObjectID]{},
		Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
}

func declarationAt(declarations lean.Array[CheckedDeclaration], index uint) CheckedDeclaration {
	return declarations.Get(index).UnwrapOr(emptyCheckedDeclaration())
}

type typeOrdinals struct {
	Declarations lean.Array[CheckedDeclaration]
	IDs          lean.Array[ObjectID]
	Ordinals     lean.OrderedMap[ObjectID, uint]
}

func assignTypeOrdinal(index uint, state typeOrdinals) typeOrdinals {
	declaration := declarationAt(state.Declarations, index)
	if declaration.Kind != CheckedNamedType {
		return state
	}
	id := declaration.Object
	return typeOrdinals{Declarations: state.Declarations, IDs: state.IDs.Push(id),
		Ordinals: state.Ordinals.Insert(id, state.IDs.Size())}
}

type checkedEdges struct {
	Ordinals lean.OrderedMap[ObjectID, uint]
	Targets  lean.Array[uint]
	Edges    lean.Array[RecursiveEdge]
}

func appendCheckedEdge(edge CheckedTypeEdge, state checkedEdges) checkedEdges {
	target := state.Ordinals.Find(edge.Target)
	if !target.IsSome() {
		return state
	}
	id := target.UnwrapOr(0)
	value := RecursiveEdge{Target: id, Direct: edge.Direct}
	return checkedEdges{Ordinals: state.Ordinals, Targets: state.Targets.Push(id), Edges: state.Edges.Push(value)}
}

func appendCheckedFieldEdges(field CheckedField, state checkedEdges) checkedEdges {
	return lean.FoldList(CheckedTypeEdges(field.Type), state, appendCheckedEdge)
}

type graphBuild struct {
	Named lean.OrderedMap[ObjectID, CheckedTypeDeclaration]
	Order typeOrdinals
	Graph lean.Array[GraphNode]
	Types lean.Array[RecursiveTypeNode]
}

func appendGraphNode(index uint, state graphBuild) graphBuild {
	id := state.Order.IDs.Get(index).UnwrapOr(0)
	empty := CheckedTypeDeclaration{Kind: UnsupportedShape, Object: 0, Fields: lean.List[CheckedField]{}, Default: 0, SelfBox: false}
	decl := state.Named.Find(id).UnwrapOr(empty)
	start := checkedEdges{Ordinals: state.Order.Ordinals, Targets: lean.Array[uint]{}, Edges: lean.Array[RecursiveEdge]{}}
	edges := lean.FoldList(decl.Fields, start, appendCheckedFieldEdges)
	graph := state.Graph.Push(GraphNode{Edges: edges.Targets})
	node := RecursiveTypeNode{Edges: edges.Edges, Enum: decl.Kind == EnumShape, SelfBox: decl.SelfBox}
	return graphBuild{Named: state.Named, Order: state.Order, Graph: graph, Types: state.Types.Push(node)}
}

type packageGroupBuild struct {
	Graph        graphBuild
	Membership   componentMembership
	Condensed    lean.Array[GraphNode]
	Declarations lean.Array[CheckedDeclaration]
}

type groupEdges struct {
	Graph      lean.Array[GraphNode]
	Members    lean.Array[uint]
	Membership lean.OrderedMap[uint, uint]
	Candidates lean.Array[uint]
	Targets    lean.Array[uint]
}

func appendCondensedEdge(index uint, state groupEdges) groupEdges {
	target := state.Candidates.Get(index).UnwrapOr(0)
	group := state.Membership.Find(target)
	if !group.IsSome() {
		return state
	}
	return groupEdges{Graph: state.Graph, Members: state.Members, Membership: state.Membership,
		Candidates: state.Candidates, Targets: state.Targets.Push(group.UnwrapOr(0))}
}

func appendGroupNode(index uint, state groupEdges) groupEdges {
	id := state.Members.Get(index).UnwrapOr(0)
	edges := state.Graph.Get(id).UnwrapOr(GraphNode{Edges: lean.Array[uint]{}}).Edges
	next := groupEdges{Graph: state.Graph, Members: state.Members, Membership: state.Membership, Candidates: edges, Targets: state.Targets}
	return lean.FoldN(edges.Size(), next, appendCondensedEdge)
}

type groupMembers struct {
	Ordered lean.Array[ObjectID]
	Members lean.Array[uint]
	IDs     lean.Array[ObjectID]
}

func appendGroupMember(index uint, state groupMembers) groupMembers {
	ordinal := state.Members.Get(index).UnwrapOr(0)
	id := state.Ordered.Get(ordinal).UnwrapOr(0)
	return groupMembers{Ordered: state.Ordered, Members: state.Members, IDs: state.IDs.Push(id)}
}

func groupedDeclaration(ids lean.Array[ObjectID]) CheckedDeclaration {
	if ids.Size() == 1 {
		return CheckedDeclaration{Kind: CheckedNamedType, Object: ids.Get(0).UnwrapOr(0), Type: noCheckedType(),
			Group: lean.Array[ObjectID]{}, Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
	}
	return CheckedDeclaration{Kind: CheckedMutualTypes, Object: 0, Type: noCheckedType(),
		Group: ids, Function: lean.None[CheckedFunction](), Contract: lean.None[CheckedContractDeclaration]()}
}

func appendCondensedGroup(index uint, state packageGroupBuild) packageGroupBuild {
	members := state.Membership.Groups.Get(index).UnwrapOr(lean.Array[uint]{})
	edges := groupEdges{Graph: state.Graph.Graph, Members: members, Membership: state.Membership.Membership,
		Candidates: lean.Array[uint]{}, Targets: lean.Array[uint]{}}
	condensed := lean.FoldN(members.Size(), edges, appendGroupNode)
	ids := groupMembers{Ordered: state.Graph.Order.IDs, Members: members, IDs: lean.Array[ObjectID]{}}
	declaration := groupedDeclaration(lean.FoldN(members.Size(), ids, appendGroupMember).IDs)
	return packageGroupBuild{Graph: state.Graph, Membership: state.Membership, Condensed: state.Condensed.Push(GraphNode{Edges: condensed.Targets}),
		Declarations: state.Declarations.Push(declaration)}
}

type groupRoots struct {
	GroupBuild packageGroupBuild
	Roots      lean.Array[uint]
}

func assignGroupRoot(index uint, state groupRoots) groupRoots {
	order := state.GroupBuild.Graph.Order
	decl := declarationAt(order.Declarations, index)
	absent := state.GroupBuild.Condensed.Size()
	if decl.Kind != CheckedNamedType {
		return groupRoots{GroupBuild: state.GroupBuild, Roots: state.Roots.Push(absent)}
	}
	ordinal := order.Ordinals.Find(decl.Object).UnwrapOr(order.IDs.Size())
	root := state.GroupBuild.Membership.Membership.Find(ordinal).UnwrapOr(absent)
	return groupRoots{GroupBuild: state.GroupBuild, Roots: state.Roots.Push(root)}
}

type groupPlacementState struct {
	Build      packageGroupBuild
	Placements lean.Array[GraphPlacement]
	Next, Root uint
	Result     lean.Array[CheckedDeclaration]
}

func appendPlacedGroup(_ uint, state groupPlacementState) lean.FoldControl[groupPlacementState] {
	next := state.Placements.Get(state.Next)
	if !next.IsSome() {
		return lean.FoldControl[groupPlacementState]{State: state, Stop: true}
	}
	item := next.UnwrapOr(GraphPlacement{RootIndex: 0, Node: 0})
	if item.RootIndex != state.Root {
		return lean.FoldControl[groupPlacementState]{State: state, Stop: true}
	}
	decl := declarationAt(state.Build.Declarations, item.Node)
	updated := groupPlacementState{Build: state.Build, Placements: state.Placements,
		Next: state.Next + 1, Root: state.Root, Result: state.Result.Push(decl)}
	return lean.FoldControl[groupPlacementState]{State: updated, Stop: false}
}

func appendGroupPlacement(index uint, state groupPlacementState) groupPlacementState {
	cursor := groupPlacementState{Build: state.Build, Placements: state.Placements,
		Next: state.Next, Root: index, Result: state.Result}
	inserted := lean.FoldNUntil(state.Placements.Size()-state.Next, cursor, appendPlacedGroup).State
	decl := declarationAt(state.Build.Graph.Order.Declarations, index)
	if decl.Kind != CheckedNamedType {
		return groupPlacementState{Build: state.Build, Placements: state.Placements,
			Next: inserted.Next, Root: index, Result: inserted.Result.Push(decl)}
	}
	return inserted
}

func arrangeGroups(graph graphBuild, groups Components) PackageGroups {
	start := componentMembership{Groups: groups.Groups, Membership: lean.OrderedMap[uint, uint]{}}
	membership := lean.FoldN(groups.Groups.Size(), start, indexGroup)
	initial := packageGroupBuild{Graph: graph, Membership: membership, Condensed: lean.Array[GraphNode]{},
		Declarations: lean.Array[CheckedDeclaration]{}}
	built := lean.FoldN(groups.Groups.Size(), initial, appendCondensedGroup)
	roots := groupRoots{GroupBuild: built, Roots: lean.Array[uint]{}}
	rootOrder := lean.FoldN(graph.Order.Declarations.Size(), roots, assignGroupRoot)
	placed := OrderDependencies(built.Condensed, rootOrder.Roots)
	initialPlacement := groupPlacementState{Build: built, Placements: placed.Placements, Next: 0, Root: 0,
		Result: lean.Array[CheckedDeclaration]{}}
	result := lean.FoldN(graph.Order.Declarations.Size(), initialPlacement, appendGroupPlacement)
	return PackageGroups{Declarations: result.Result, Problem: ValidRecursiveTypes, Complete: placed.Complete, From: 0, To: 0}
}

// GroupPackageTypes validates recursive declarations and orders their groups.
//
//golean:export
func GroupPackageTypes(declarations lean.Array[CheckedDeclaration], named lean.OrderedMap[ObjectID, CheckedTypeDeclaration]) PackageGroups {
	start := typeOrdinals{Declarations: declarations, IDs: lean.Array[ObjectID]{}, Ordinals: lean.OrderedMap[ObjectID, uint]{}}
	order := lean.FoldN(declarations.Size(), start, assignTypeOrdinal)
	initial := graphBuild{Named: named, Order: order, Graph: lean.Array[GraphNode]{}, Types: lean.Array[RecursiveTypeNode]{}}
	graph := lean.FoldN(order.IDs.Size(), initial, appendGraphNode)
	groups := StrongComponents(graph.Graph)
	if !groups.Complete {
		return PackageGroups{Declarations: declarations, Problem: ValidRecursiveTypes, Complete: false, From: 0, To: 0}
	}
	checks := CheckRecursiveTypes(graph.Types, groups)
	if checks.Problem != ValidRecursiveTypes {
		return PackageGroups{Declarations: declarations, Problem: checks.Problem, Complete: true,
			From: order.IDs.Get(checks.Source).UnwrapOr(0), To: order.IDs.Get(checks.Target).UnwrapOr(0)}
	}
	return arrangeGroups(graph, groups)
}
