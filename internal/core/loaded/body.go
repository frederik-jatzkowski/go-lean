package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// BodyCursor identifies the remaining statements and their continuation.
type BodyCursor struct {
	Statements lean.Array[StmtID]
	Index      uint
	Tail       uint
}

func (c BodyCursor) HasStatements() bool {
	return c.Index < c.Statements.Size()
}

// BodyTail describes a suffix that may be inlined once or shared by jumps.
type BodyTail struct {
	Suffix     BodyCursor
	Join       int
	Jump, Used bool
	Value      CheckedExprID
}

type BodyFrameKind uint8

const (
	VisitBlock BodyFrameKind = iota + 1
	CacheTail
	WrapBindings
	CompleteThen
	CompleteElse
	CompleteJoin
	VisitCase
	CompleteCase
	CompleteMatch
)

// BodyFrame is a pending step in function-body traversal.
type BodyFrame struct {
	Kind                   BodyFrameKind
	Cursor                 BodyCursor
	Tail                   uint
	Match                  uint
	Condition, Yes, Branch CheckedExprID
	Bindings               lean.Array[CheckedLetBinding]
}

type BodyEffect uint8

const (
	BodyContinue BodyEffect = iota
	BodyVisitStatement
	BodyVisitMatchCase
	BodyCompleteMatchCase
	BodyMissingReturn
	BodyUnreachableSuffix
)

// BodyTransition holds the next pure state and any request for the caller.
type BodyTransition struct {
	State  BodyState
	Effect BodyEffect
	Cursor BodyCursor
	Match  uint
}

// BodyFrameStack is a persistent stack of pending frames.
type BodyFrameStack struct {
	Frame    BodyFrame
	Previous lean.Box[BodyFrameStack]
}

// BodyState stores pending work and values produced by completed frames.
type BodyState struct {
	Frames  lean.Box[BodyFrameStack]
	Tails   lean.Array[BodyTail]
	Matches lean.Array[BodyMatch]
	Value   CheckedExprID
	Nodes   lean.Array[CheckedExpr]
}

func emptyCursor() BodyCursor {
	return BodyCursor{Statements: lean.Array[StmtID]{}, Index: 0, Tail: 0}
}

func emptyTail() BodyTail {
	return BodyTail{Suffix: emptyCursor(), Join: 0, Jump: false, Used: false, Value: 0}
}

// Push schedules a frame above the current work.
//
//golean:export
func (s BodyState) Push(frame BodyFrame) BodyState {
	stack := lean.NewBox(BodyFrameStack{Frame: frame, Previous: s.Frames})
	return BodyState{Nodes: s.Nodes, Matches: s.Matches, Frames: stack, Tails: s.Tails, Value: s.Value}
}

// Visit schedules the remainder of a block.
//
//golean:export
func (s BodyState) Visit(cursor BodyCursor) BodyState {
	frame := BodyFrame{Kind: VisitBlock, Cursor: cursor, Tail: 0, Match: 0, Condition: 0,
		Yes: 0, Branch: 0, Bindings: lean.Array[CheckedLetBinding]{}}
	return s.Push(frame)
}

// WithValue records an expression returned by a requested operation.
//
//golean:export
func (s BodyState) WithValue(value CheckedExprID) BodyState {
	return BodyState{Nodes: s.Nodes, Matches: s.Matches, Frames: s.Frames, Tails: s.Tails, Value: value}
}

// AddTail allocates a suffix after all earlier ones.
//
//golean:export
func (s BodyState) AddTail(tail BodyTail) BodyState {
	return BodyState{Nodes: s.Nodes, Matches: s.Matches, Frames: s.Frames, Tails: s.Tails.Push(tail), Value: s.Value}
}

// Tail retrieves a suffix by its allocation index.
//
//golean:export
func (s BodyState) Tail(id uint) BodyTail {
	if id == 0 {
		return emptyTail()
	}
	return s.Tails.Get(id - 1).UnwrapOr(emptyTail())
}

func (s BodyState) setTail(id uint, tail BodyTail) BodyState {
	if id == 0 {
		return s
	}
	return BodyState{Nodes: s.Nodes, Matches: s.Matches, Frames: s.Frames, Tails: s.Tails.Set(id-1, tail), Value: s.Value}
}

func usedTail(t BodyTail, value CheckedExprID) BodyTail {
	return BodyTail{Suffix: t.Suffix, Join: t.Join, Jump: t.Jump, Used: true, Value: value}
}

func nextBody(s BodyState) BodyTransition {
	return BodyTransition{State: s, Effect: BodyContinue, Cursor: emptyCursor(), Match: 0}
}

func (s BodyState) followTail(id uint) BodyTransition {
	if id == 0 {
		return BodyTransition{State: s, Effect: BodyMissingReturn, Cursor: emptyCursor(), Match: 0}
	}
	tail := s.Tail(id)
	if tail.Jump {
		updated := s.setTail(id, usedTail(tail, tail.Value))
		return nextBody(updated.addNode(controlRecipe(CheckedJump, tail.Join, lean.Array[CheckedExprID]{}, lean.Array[CheckedMatchCase]{})))
	}
	if tail.Used {
		return nextBody(s.WithValue(tail.Value))
	}
	cache := BodyFrame{Kind: CacheTail, Cursor: emptyCursor(), Tail: id, Match: 0, Condition: 0,
		Yes: 0, Branch: 0, Bindings: lean.Array[CheckedLetBinding]{}}
	return nextBody(s.Push(cache).Visit(tail.Suffix))
}

func (s BodyState) finishConditional(frame BodyFrame) BodyTransition {
	tail := s.Tail(frame.Tail)
	args := lean.Array[CheckedExprID]{}.Push(frame.Condition).Push(frame.Yes).Push(s.Value)
	node := controlRecipe(CheckedIf, 0, args, lean.Array[CheckedMatchCase]{})
	branch := s.addNode(node)
	if tail.Jump {
		join := BodyFrame{Kind: CompleteJoin, Cursor: emptyCursor(), Tail: frame.Tail, Match: 0, Condition: 0,
			Yes: 0, Branch: branch.Value, Bindings: lean.Array[CheckedLetBinding]{}}
		return nextBody(branch.Push(join).Visit(tail.Suffix))
	}
	if !tail.Used && tail.Suffix.HasStatements() {
		return BodyTransition{State: s, Effect: BodyUnreachableSuffix, Cursor: tail.Suffix, Match: 0}
	}
	return nextBody(branch)
}

// AdvanceBody executes one pending frame. Source validation and expression
// lowering are requested by value when the next frame needs them.
//
//golean:export
func AdvanceBody(s BodyState) BodyTransition {
	if !s.Frames.IsSome() {
		return nextBody(s)
	}
	top := s.Frames.Get()
	rest := BodyState{Nodes: s.Nodes, Matches: s.Matches, Frames: top.Previous, Tails: s.Tails, Value: s.Value}
	return rest.advanceFrame(top.Frame)
}

func (s BodyState) advanceFrame(frame BodyFrame) BodyTransition {
	if frame.Kind == VisitBlock {
		if frame.Cursor.HasStatements() {
			return BodyTransition{State: s, Effect: BodyVisitStatement, Cursor: frame.Cursor, Match: 0}
		}
		return s.followTail(frame.Cursor.Tail)
	}
	if frame.Kind == CacheTail {
		return nextBody(s.setTail(frame.Tail, usedTail(s.Tail(frame.Tail), s.Value)))
	}
	if frame.Kind == WrapBindings {
		return nextBody(s.wrapLetBindings(frame.Bindings))
	}
	if frame.Kind == CompleteThen {
		finish := BodyFrame{Kind: CompleteElse, Cursor: emptyCursor(), Tail: frame.Tail, Match: 0, Condition: frame.Condition,
			Yes: s.Value, Branch: 0, Bindings: lean.Array[CheckedLetBinding]{}}
		other := BodyCursor{Statements: frame.Cursor.Statements, Index: 0, Tail: frame.Tail}
		return nextBody(s.Push(finish).Visit(other))
	}
	if frame.Kind == CompleteElse {
		return s.finishConditional(frame)
	}
	if frame.Kind == CompleteJoin {
		tail := s.Tail(frame.Tail)
		node := controlRecipe(CheckedJoin, tail.Join, expressionOperands(s.Value, frame.Branch, true), lean.Array[CheckedMatchCase]{})
		return nextBody(s.addNode(node))
	}
	if frame.Kind == VisitCase {
		return BodyTransition{State: s, Effect: BodyVisitMatchCase, Cursor: emptyCursor(), Match: frame.Match}
	}
	if frame.Kind == CompleteCase {
		return BodyTransition{State: s, Effect: BodyCompleteMatchCase, Cursor: emptyCursor(), Match: frame.Match}
	}
	if frame.Kind == CompleteMatch {
		return nextBody(s.WithValue(frame.Branch))
	}
	return nextBody(s)
}

func (s BodyState) addNode(node CheckedExpr) BodyState {
	nodes := s.Nodes.Push(node)
	return BodyState{Nodes: nodes, Matches: s.Matches, Frames: s.Frames, Tails: s.Tails, Value: CheckedExprID(nodes.Size())}
}

// WithCheckedExpression records all nodes checked in a requested expression.
//
//golean:export
func (s BodyState) WithCheckedExpression(walk ExprWalk) BodyState {
	return BodyState{Nodes: walk.Nodes, Matches: s.Matches, Frames: s.Frames, Tails: s.Tails, Value: walk.Value}
}

type checkedLets struct {
	Bindings lean.Array[CheckedLetBinding]
	Body     BodyState
}

func wrapCheckedLet(index uint, state checkedLets) checkedLets {
	binding := state.Bindings.Get(state.Bindings.Size() - 1 - index).UnwrapOr(CheckedLetBinding{Binding: 0, Value: 0})
	operands := expressionOperands(binding.Value, state.Body.Value, true)
	node := controlRecipe(CheckedLet, binding.Binding, operands, lean.Array[CheckedMatchCase]{})
	return checkedLets{Bindings: state.Bindings, Body: state.Body.addNode(node)}
}

func (s BodyState) wrapLetBindings(bindings lean.Array[CheckedLetBinding]) BodyState {
	return lean.FoldN(bindings.Size(), checkedLets{Bindings: bindings, Body: s}, wrapCheckedLet).Body
}

// AppendZero records the zero value of an already checked type.
//
//golean:export
func (s BodyState) AppendZero(t CheckedType) BodyState {
	return s.addNode(recipe(CheckedZero, t, 0, "", 0, false, lean.Array[CheckedExprID]{}))
}
