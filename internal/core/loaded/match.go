package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// MatchCoverage keeps enum payload order separately from the remaining set.
type MatchCoverage struct {
	Payloads  lean.Array[ObjectID]
	Remaining lean.OrderedSet[ObjectID]
}

func addMatchPayload(index uint, coverage MatchCoverage) MatchCoverage {
	payload := coverage.Payloads.Get(index).UnwrapOr(0)
	return MatchCoverage{Payloads: coverage.Payloads, Remaining: coverage.Remaining.Insert(payload)}
}

// NewMatchCoverage starts an enum switch with every payload unhandled.
//
//golean:export
func NewMatchCoverage(payloads lean.Array[ObjectID]) MatchCoverage {
	initial := MatchCoverage{Payloads: payloads, Remaining: lean.OrderedSet[ObjectID]{}}
	return lean.FoldN(payloads.Size(), initial, addMatchPayload)
}

// ValidateCase checks a clause before its body is visited.
//
//golean:export
func (c MatchCoverage) ValidateCase(clause SwitchClause) Diagnostic {
	shape := clause.Validate()
	if shape.Code != Valid {
		return shape
	}
	if !c.Remaining.Contains(clause.Variant) {
		return Diagnostic{Code: UnhandledEnumPayload, Pos: clause.Pos, Detail: ""}
	}
	return validDiagnostic()
}

// MarkCase records a successfully validated clause.
//
//golean:export
func (c MatchCoverage) MarkCase(id ObjectID) MatchCoverage {
	return MatchCoverage{Payloads: c.Payloads, Remaining: c.Remaining.Erase(id)}
}

type missingMatchPayload struct {
	Coverage MatchCoverage
	Missing  ObjectID
}

func findMissingPayload(index uint, check missingMatchPayload) lean.FoldControl[missingMatchPayload] {
	id := check.Coverage.Payloads.Get(index).UnwrapOr(0)
	if check.Coverage.Remaining.Contains(id) {
		return lean.FoldControl[missingMatchPayload]{State: missingMatchPayload{Coverage: check.Coverage, Missing: id}, Stop: true}
	}
	return lean.FoldControl[missingMatchPayload]{State: check, Stop: false}
}

// MissingCase returns the first unhandled payload in the enum's declared order.
//
//golean:export
func (c MatchCoverage) MissingCase() ObjectID {
	initial := missingMatchPayload{Coverage: c, Missing: 0}
	return lean.FoldNUntil(c.Payloads.Size(), initial, findMissingPayload).State.Missing
}
