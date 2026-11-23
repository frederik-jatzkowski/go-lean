package bowling

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// Play parses comma-separated pin counts and replays them from a new game.
func Play(input lean.ByteArray) lean.Option[replayResult] { return playInput(input) }

type token struct {
	pins  int64
	comma bool
}

type lexer struct {
	input   lean.ByteArray
	tokens  lean.List[token]
	pending bool
}

func flushOne(state lexer) lexer {
	if !state.pending {
		return state
	}
	return lexer{input: state.input, tokens: lean.Cons(token{pins: 1, comma: false}, state.tokens), pending: false}
}

// digit decodes a byte already checked to be in '0' through '9'.
func digit(value byte) int64 {
	if value == '0' {
		return 0
	}
	if value == '1' {
		return 1
	}
	if value == '2' {
		return 2
	}
	if value == '3' {
		return 3
	}
	if value == '4' {
		return 4
	}
	if value == '5' {
		return 5
	}
	if value == '6' {
		return 6
	}
	if value == '7' {
		return 7
	}
	if value == '8' {
		return 8
	}
	return 9
}

func lexByte(index uint, state lexer) lean.FoldControl[lexer] {
	byteValue := state.input.Get(index).UnwrapOr(0)
	// A pending '1' combines with the next byte only if it is '0'.
	if state.pending && byteValue == '0' {
		next := lexer{input: state.input, tokens: lean.Cons(token{pins: 10, comma: false}, state.tokens), pending: false}
		return lean.FoldControl[lexer]{State: next, Stop: false}
	}
	return scanSingle(byteValue, flushOne(state))
}

func scanSingle(byteValue byte, base lexer) lean.FoldControl[lexer] {
	if byteValue == '1' {
		next := lexer{input: base.input, tokens: base.tokens, pending: true}
		return lean.FoldControl[lexer]{State: next, Stop: false}
	}
	if byteValue >= '0' && byteValue <= '9' {
		next := lexer{input: base.input, tokens: lean.Cons(token{pins: digit(byteValue), comma: false}, base.tokens), pending: false}
		return lean.FoldControl[lexer]{State: next, Stop: false}
	}
	if byteValue == ',' {
		next := lexer{input: base.input, tokens: lean.Cons(token{pins: 0, comma: true}, base.tokens), pending: false}
		return lean.FoldControl[lexer]{State: next, Stop: false}
	}
	if byteValue == ' ' || byteValue == '\t' || byteValue == '\r' || byteValue == '\n' {
		return lean.FoldControl[lexer]{State: base, Stop: false}
	}
	return lean.FoldControl[lexer]{State: base, Stop: true}
}

// lex returns tokens in reverse order, allowing the parser to build the
// attempts in input order by prepending.
func lex(input lean.ByteArray) lean.Option[lean.List[token]] {
	initial := lexer{input: input, tokens: lean.Nil[token](), pending: false}
	result := lean.FoldNUntil(input.Size(), initial, lexByte)
	if result.Stop {
		return lean.None[lean.List[token]]()
	}
	return lean.Some(flushOne(result.State).tokens)
}

type parser struct {
	attempts   lean.List[int64]
	afterCount bool
}

func parseToken(current token, state parser) lean.FoldControl[parser] {
	if current.comma != state.afterCount {
		return lean.FoldControl[parser]{State: state, Stop: true}
	}
	if current.comma {
		next := parser{attempts: state.attempts, afterCount: false}
		return lean.FoldControl[parser]{State: next, Stop: false}
	}
	next := parser{attempts: lean.Cons(current.pins, state.attempts), afterCount: true}
	return lean.FoldControl[parser]{State: next, Stop: false}
}

func parse(tokens lean.List[token]) lean.Option[lean.List[int64]] {
	initial := parser{attempts: lean.Nil[int64](), afterCount: false}
	result := lean.FoldListUntil(tokens, initial, parseToken)
	return finishParse(result)
}

func finishParse(result lean.FoldControl[parser]) lean.Option[lean.List[int64]] {
	if result.Stop || (!result.State.afterCount && !result.State.attempts.IsEmpty()) {
		return lean.None[lean.List[int64]]()
	}
	return lean.Some(result.State.attempts)
}

//golean:export
func playInput(input lean.ByteArray) lean.Option[replayResult] {
	tokens := lex(input)
	if !tokens.IsSome() {
		return lean.None[replayResult]()
	}
	attempts := parse(tokens.UnwrapOr(lean.Nil[token]()))
	if !attempts.IsSome() {
		return lean.None[replayResult]()
	}
	return lean.Some(Replay(attempts.UnwrapOr(lean.Nil[int64]())))
}
