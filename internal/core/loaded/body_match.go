package loaded

import (
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

// BodyMatch stores case coverage and completed arms while lowering the match.
type BodyMatch struct {
	Pos        string
	Value      CheckedExprID
	Clauses    lean.Array[SwitchClause]
	Coverage   MatchCoverage
	Cases      lean.Array[CheckedMatchCase]
	Next, Tail uint
	Binding    int
}

func emptyBodyMatch() BodyMatch {
	return BodyMatch{Pos: "", Value: 0, Clauses: lean.Array[SwitchClause]{},
		Coverage: NewMatchCoverage(lean.Array[ObjectID]{}), Cases: lean.Array[CheckedMatchCase]{}, Next: 0, Tail: 0, Binding: -1}
}

// BeginMatch allocates a frame for the first case of a switch.
//
//golean:export
func (s BodyState) BeginMatch(pos string, value CheckedExprID, clauses lean.Array[SwitchClause], payloads lean.Array[ObjectID], tail uint) BodyState {
	match := BodyMatch{Pos: pos, Value: value, Clauses: clauses,
		Coverage: NewMatchCoverage(payloads), Cases: lean.Array[CheckedMatchCase]{}, Next: 0, Tail: tail, Binding: -1}
	matches := s.Matches.Push(match)
	next := BodyState{Nodes: s.Nodes, Matches: matches, Frames: s.Frames, Tails: s.Tails, Value: s.Value}
	return next.Push(matchFrame(VisitCase, matches.Size()))
}

func matchFrame(kind BodyFrameKind, id uint) BodyFrame {
	return BodyFrame{Kind: kind, Cursor: emptyCursor(), Tail: 0, Match: id, Condition: 0,
		Yes: 0, Branch: 0, Bindings: lean.Array[CheckedLetBinding]{}}
}

// Match returns the state reserved for a switch.
//
//golean:export
func (s BodyState) Match(id uint) BodyMatch {
	if id == 0 {
		return emptyBodyMatch()
	}
	return s.Matches.Get(id - 1).UnwrapOr(emptyBodyMatch())
}

func (s BodyState) setMatch(id uint, match BodyMatch) BodyState {
	if id == 0 {
		return s
	}
	return BodyState{Nodes: s.Nodes, Matches: s.Matches.Set(id-1, match), Frames: s.Frames, Tails: s.Tails, Value: s.Value}
}

// Clause returns the current case. An absent case calls for completion.
//
//golean:export
func (m BodyMatch) Clause() lean.Option[SwitchClause] {
	return m.Clauses.Get(m.Next)
}

// BeginCase schedules a validated arm with its assigned binding ID.
//
//golean:export
func (s BodyState) BeginCase(id uint, clause SwitchClause, binding int) BodyState {
	match := s.Match(id)
	advanced := BodyMatch{Pos: match.Pos, Value: match.Value, Clauses: match.Clauses,
		Coverage: match.Coverage.MarkCase(clause.Variant), Cases: match.Cases, Next: match.Next, Tail: match.Tail, Binding: binding}
	cursor := BodyCursor{Statements: clause.Body, Index: 0, Tail: match.Tail}
	return s.setMatch(id, advanced).Push(matchFrame(CompleteCase, id)).Visit(cursor)
}

// EndCase adds the lowered arm and schedules the next case.
//
//golean:export
func (s BodyState) EndCase(id uint, variant string) BodyState {
	match := s.Match(id)
	cases := match.Cases.Push(CheckedMatchCase{Variant: variant, Binding: match.Binding, Value: s.Value})
	advanced := BodyMatch{Pos: match.Pos, Value: match.Value, Clauses: match.Clauses,
		Coverage: match.Coverage, Cases: cases, Next: match.Next + 1, Tail: match.Tail, Binding: -1}
	return s.setMatch(id, advanced).Push(matchFrame(VisitCase, id))
}

// FinishMatch constructs an exhaustive switch. A trailing suffix is still
// visited when Go requires one after a switch whose cases all return.
//
//golean:export
func (s BodyState) FinishMatch(match BodyMatch) BodyState {
	node := controlRecipe(CheckedMatch, 0, expressionOperands(match.Value, 0, false), match.Cases)
	result := s.addNode(node)
	tail := s.Tail(match.Tail)
	if tail.Used {
		join := BodyFrame{Kind: CompleteJoin, Cursor: emptyCursor(), Tail: match.Tail, Match: 0, Condition: 0,
			Yes: 0, Branch: result.Value, Bindings: lean.Array[CheckedLetBinding]{}}
		return result.Push(join).Visit(tail.Suffix)
	}
	if tail.Suffix.HasStatements() {
		discard := BodyFrame{Kind: CompleteMatch, Cursor: emptyCursor(), Tail: 0, Match: 0, Condition: 0,
			Yes: 0, Branch: result.Value, Bindings: lean.Array[CheckedLetBinding]{}}
		return result.Push(discard).Visit(tail.Suffix)
	}
	return result
}
