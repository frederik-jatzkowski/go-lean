package lower

// Input describes the checked source program through stable positive IDs.
// Zero denotes an absent reference. Field selectors belong to a source record
// kind. Records and references must match the typed schema in input_graph.go.
// FunctionAt enumerates all checked functions in dependency-first order. The
// root's package is the Go import path of the source file being lowered.
// Implementations must return normally, with stable answers throughout lowering.
// Ordinary operands dominate their use, and phi operands are available on
// their corresponding incoming edges. Nonrecursive calls that are not
// builtins or interface invocations refer to an earlier checked definition.
// The declared types of operands, fields and results agree with their uses.
// Counted loops and folds identify the header, exit, ordered initial values
// and equally sized back-edge updates. Slice builds identify the destination,
// source, and the validated reads and writes. Chain recursion identifies the
// smaller tail argument. Stateful descriptors identify the receiver, its
// fields, and, when present, the callback and indexed-loop shape.
//
//golean:assume reference_counts : ∀ s id field, 0 ≤ ReferenceCount s id field
//golean:assume text_counts : ∀ s id field, 0 ≤ TextCount s id field
//golean:assume function_counts : ∀ s, 0 ≤ FunctionCount s
//golean:assume function_order : ∀ s i, 0 ≤ i → i < FunctionCount s → 0 < FunctionAt s i ∧ FunctionOrder s (FunctionAt s i) = i
//golean:assume reference_exists : ∀ s id field i, 0 ≤ i → i < ReferenceCount s id field → ReferenceAt s id field i ≠ 0 → HasRecord s (ReferenceAt s id field i) = true
//golean:assume call_dependency_order : ∀ s call, HasOrderedCall s call = true → 0 ≤ FunctionOrder s (CallTarget s call) ∧ FunctionOrder s (CallTarget s call) < FunctionOrder s (CallOwner s call)
//golean:assume ordinary_dominance : ∀ s instruction i, 0 ≤ i → i < OrdinaryOperandCount s instruction → HasRecord s (OrdinaryOperandAt s instruction i) = true ∧ OperandDominates s instruction i = true
//golean:assume structured_state : ∀ s loop, HasStructuredLoop s loop = true → 0 < LoopStateCount s loop
//golean:assume phi_arity : ∀ s phi, PhiBlock s phi ≠ 0 → PhiOperandCount s phi = PredecessorCount s (PhiBlock s phi)
//golean:assume incoming_exists : ∀ s phi pred, HasIncoming s phi pred = true → 0 < Incoming s phi pred
//golean:assume incoming_alignment : ∀ s phi pred i, 0 ≤ i → i < PredecessorCount s (PhiBlock s phi) → PredecessorAt s (PhiBlock s phi) i = pred → HasIncoming s phi pred = true ∧ Incoming s phi pred = PhiOperandAt s phi i
type Input interface {
	PackagePath() string
	FunctionCount() int64
	FunctionAt(position int64) int64
	FunctionOrder(function int64) int64
	HasRecord(id int64) bool
	HasOrderedCall(call int64) bool
	CallTarget(call int64) int64
	CallOwner(call int64) int64
	OrdinaryOperandCount(instruction int64) int64
	OrdinaryOperandAt(instruction, position int64) int64
	OperandDominates(instruction, position int64) bool
	HasStructuredLoop(loop int64) bool
	LoopStateCount(loop int64) int64
	FieldNumber(id, field int64) int64
	FieldText(id, field int64) string
	ReferenceCount(id, field int64) int64
	ReferenceAt(id, field, position int64) int64
	TextCount(id, field int64) int64
	TextAt(id, field, position int64) string
	PredecessorCount(block int64) int64
	PredecessorAt(block, position int64) int64
	PhiOperandCount(phi int64) int64
	PhiOperandAt(phi, position int64) int64
	PhiBlock(phi int64) int64
	HasIncoming(phi, predecessor int64) bool
	Incoming(phi, predecessor int64) int64
}

// StateStore models distinct namespaces for bindings and function facts.
// Updates return a new handle. Earlier handles retain their observations.
// Advance allocates the current nonnegative ID, with the maximum signed ID
// reserved as the exhaustion marker.
//
//golean:assume has_after_bind : ∀ s k v, HasBinding (Bind s k v) k = true
//golean:assume lookup_after_bind : ∀ s k v, LookupBinding (Bind s k v) k = v
//golean:assume bind_other : ∀ s k j v, j ≠ k → HasBinding (Bind s k v) j = HasBinding s j ∧ LookupBinding (Bind s k v) j = LookupBinding s j
//golean:assume bind_preserves_facts : ∀ s k v f kind, HasFact (Bind s k v) f kind = HasFact s f kind ∧ LookupFact (Bind s k v) f kind = LookupFact s f kind
//golean:assume has_after_fact : ∀ s f kind v, HasFact (PutFact s f kind v) f kind = true
//golean:assume lookup_after_fact : ∀ s f kind v, LookupFact (PutFact s f kind v) f kind = v
//golean:assume fact_other : ∀ s f kind g k v, (g ≠ f ∨ k ≠ kind) → HasFact (PutFact s f kind v) g k = HasFact s g k ∧ LookupFact (PutFact s f kind v) g k = LookupFact s g k
//golean:assume fact_preserves_bindings : ∀ s f kind v k, HasBinding (PutFact s f kind v) k = HasBinding s k ∧ LookupBinding (PutFact s f kind v) k = LookupBinding s k
//golean:assume next_nonnegative : ∀ s, 0 ≤ NextID s
//golean:assume bind_preserves_next : ∀ s k v, NextID (Bind s k v) = NextID s
//golean:assume fact_preserves_next : ∀ s f kind v, NextID (PutFact s f kind v) = NextID s
//golean:assume advance_next : ∀ s, NextID s < 9223372036854775807 → NextID (Advance s) = NextID s + 1
//golean:assume advance_exhausted : ∀ s, NextID s = 9223372036854775807 → NextID (Advance s) = NextID s
//golean:assume advance_preserves_bindings : ∀ s k, HasBinding (Advance s) k = HasBinding s k ∧ LookupBinding (Advance s) k = LookupBinding s k
//golean:assume advance_preserves_facts : ∀ s f kind, HasFact (Advance s) f kind = HasFact s f kind ∧ LookupFact (Advance s) f kind = LookupFact s f kind
//golean:assume restore_cursor : ∀ s cursor, 0 ≤ cursor → NextID (WithCursor s cursor) = cursor
//golean:assume cursor_preserves_bindings : ∀ s cursor k, HasBinding (WithCursor s cursor) k = HasBinding s k ∧ LookupBinding (WithCursor s cursor) k = LookupBinding s k
//golean:assume cursor_preserves_facts : ∀ s cursor f kind, HasFact (WithCursor s cursor) f kind = HasFact s f kind ∧ LookupFact (WithCursor s cursor) f kind = LookupFact s f kind
type StateStore interface {
	HasBinding(value int64) bool
	LookupBinding(value int64) int64
	Bind(value, binder int64) StateStore
	HasFact(function, kind int64) bool
	LookupFact(function, kind int64) int64
	PutFact(function, kind, value int64) StateStore
	NextID() int64
	Advance() StateStore
	WithCursor(cursor int64) StateStore
}

// resolveIncoming selects the operand for this path and resolves its binding.
//
//golean:verify resolvedOperandIsPresent : ∀ {I S : Type} (input : InterfaceContracts.InputContract I)
//golean:verify+   (store : InterfaceContracts.StateStoreContract S) (source : I) (state : S) (phi pred : Int64)
//golean:verify+   (found : (resolveIncoming input store source state phi pred).2.2.1 = true),
//golean:verify+   0 < (resolveIncoming input store source state phi pred).1
//golean:verify resolvesPhiOfCurrentPredecessor : ∀ {I S : Type} (input : InterfaceContracts.InputContract I)
//golean:verify+   (store : InterfaceContracts.StateStoreContract S) (source : I) (current : S)
//golean:verify+   (phi pred position : Int64) (low : 0 ≤ position)
//golean:verify+   (high : position < input.PredecessorCount source (input.PhiBlock source phi))
//golean:verify+   (predecessor : input.PredecessorAt source (input.PhiBlock source phi) position = pred)
//golean:verify+   (bound : store.HasBinding current (input.PhiOperandAt source phi position) = true),
//golean:verify+   resolveIncoming input store source current phi pred =
//golean:verify+   (input.PhiOperandAt source phi position, (store.LookupBinding current (input.PhiOperandAt source phi position),
//golean:verify+   (true, true)))
//golean:verify resolvesBranchBinding : ∀ {I S : Type} (input : InterfaceContracts.InputContract I)
//golean:verify+   (store : InterfaceContracts.StateStoreContract S) (source : I) (parent : S)
//golean:verify+   (phi pred value binder : Int64) (incoming : input.HasIncoming source phi pred = true)
//golean:verify+   (selected : input.Incoming source phi pred = value),
//golean:verify+   resolveIncoming input store source (store.Bind parent value binder) phi pred =
//golean:verify+   (value, (binder, (true, true)))
//golean:verify branchUpdatePreservesSiblingResolution : ∀ {I S : Type} (input : InterfaceContracts.InputContract I)
//golean:verify+   (store : InterfaceContracts.StateStoreContract S) (source : I) (parent : S)
//golean:verify+   (phi sibling key binder : Int64) (distinct : input.Incoming source phi sibling ≠ key),
//golean:verify+   resolveIncoming input store source (store.Bind parent key binder) phi sibling =
//golean:verify+   resolveIncoming input store source parent phi sibling
//golean:verify carryingCursorPreservesIncomingResolution : ∀ {I S : Type} (input : InterfaceContracts.InputContract I)
//golean:verify+   (store : InterfaceContracts.StateStoreContract S) (source : I) (parent : S) (phi pred cursor : Int64),
//golean:verify+   resolveIncoming input store source (store.WithCursor parent cursor) phi pred =
//golean:verify+   resolveIncoming input store source parent phi pred
func resolveIncoming(input Input, state StateStore, phi, predecessor int64) (operand, binder int64, incoming, bound bool) {
	if !input.HasIncoming(phi, predecessor) {
		return 0, 0, false, false
	}
	operand = input.Incoming(phi, predecessor)
	if !state.HasBinding(operand) {
		return operand, 0, true, false
	}
	return operand, state.LookupBinding(operand), true, true
}
