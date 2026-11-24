// Package compiler translates typed prefix expressions to stack bytecode.
//
//golean:verify:import spec
//golean:verify all : let observe := fun result : machineResult =>
//golean:verify+     let state := result.«field:State»
//golean:verify+     (result.«field:Status», StackMachineCompiler.Spec.State.mk
//golean:verify+       state.«field:PC».toNat state.«field:Stack»)
//golean:verify+   StackMachineCompiler.Spec.Requirements.all
//golean:verify+     (fun source =>
//golean:verify+       let result := Compile source
//golean:verify+       let err := result.«field:Error»
//golean:verify+       ⟨result.«field:Code», result.«field:Type», err.«field:Kind», err.«field:Offset».toNat⟩)
//golean:verify+     (fun code pc stack aligned => observe (Step code ⟨pc, stack⟩ aligned))
//golean:verify+     (fun code => observe (RunCode code))
package compiler

import (
	"math"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type Type uint8

const (
	U8 Type = iota + 1
	Bool
)

type DiagnosticKind uint8

const (
	NoDiagnostic DiagnosticKind = iota
	CodeTooLarge
	InvalidLexeme
	SyntaxError
	TypeMismatch
)

const (
	integerToken byte = iota + 1
	booleanToken
	addToken
	subToken
	eqToken
	ltToken
	andToken
	notToken
)

type lexeme struct {
	Kind   byte
	Value  byte
	Offset uint
}

type Diagnostic struct {
	Kind   DiagnosticKind
	Offset uint
}

func noDiagnostic() Diagnostic {
	return Diagnostic{Kind: NoDiagnostic, Offset: 0}
}

func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

type classification struct {
	Kind  byte
	Value byte
}

func timesTen(n byte) byte {
	twice := n + n
	four := twice + twice
	return four + four + twice
}

func decimal(a, b, c byte, width uint) classification {
	invalid := classification{Kind: 0, Value: 0}
	if !isDigit(a) {
		return invalid
	}
	if width == 1 {
		return classification{Kind: integerToken, Value: a - '0'}
	}
	if a == '0' || !isDigit(b) {
		return invalid
	}
	prefix := timesTen(a-'0') + (b - '0')
	if width == 2 {
		return classification{Kind: integerToken, Value: prefix}
	}
	if width != 3 || !isDigit(c) {
		return invalid
	}
	if a > '2' || (a == '2' && (b > '5' || (b == '5' && c > '5'))) {
		return invalid
	}
	return classification{Kind: integerToken, Value: timesTen(prefix) + (c - '0')}
}

func classify(source lean.ByteArray) classification {
	width := source.Size()
	a := source.Get(0).UnwrapOr(0)
	b := source.Get(1).UnwrapOr(0)
	c := source.Get(2).UnwrapOr(0)
	if width == 2 {
		if a == 'e' && b == 'q' {
			return classification{Kind: eqToken, Value: 0}
		}
		if a == 'l' && b == 't' {
			return classification{Kind: ltToken, Value: 0}
		}
	}
	if width == 3 {
		if a == 'a' && b == 'd' && c == 'd' {
			return classification{Kind: addToken, Value: 0}
		}
		if a == 's' && b == 'u' && c == 'b' {
			return classification{Kind: subToken, Value: 0}
		}
		if a == 'a' && b == 'n' && c == 'd' {
			return classification{Kind: andToken, Value: 0}
		}
		if a == 'n' && b == 'o' && c == 't' {
			return classification{Kind: notToken, Value: 0}
		}
	}
	if width == 4 && a == 't' && b == 'r' && c == 'u' && source.Get(3).UnwrapOr(0) == 'e' {
		return classification{Kind: booleanToken, Value: 1}
	}
	if width == 5 && a == 'f' && b == 'a' && c == 'l' &&
		source.Get(3).UnwrapOr(0) == 's' && source.Get(4).UnwrapOr(0) == 'e' {
		return classification{Kind: booleanToken, Value: 0}
	}
	return decimal(a, b, c, width)
}

type scanState struct {
	Start  uint
	InWord bool
}

type scanResult struct {
	State  scanState
	Closed bool
}

func scanByte(state scanState, index uint, b byte) scanResult {
	if isSpace(b) {
		return scanResult{State: scanState{Start: state.Start, InWord: false}, Closed: state.InWord}
	}
	if state.InWord {
		return scanResult{State: state, Closed: false}
	}
	return scanResult{State: scanState{Start: index, InWord: true}, Closed: false}
}

type lexer struct {
	Source lean.ByteArray
	Words  lean.Array[lexeme]
	Scan   scanState
	Error  Diagnostic
}

func scanSourceByte(index uint, state lexer) lean.FoldControl[lexer] {
	scanned := scanByte(state.Scan, index, state.Source.Get(index).UnwrapOr(' '))
	if !scanned.Closed {
		return lean.FoldControl[lexer]{State: lexer{Source: state.Source, Words: state.Words, Scan: scanned.State, Error: state.Error}, Stop: false}
	}
	return closeWord(index, state, scanned.State)
}

func closeWord(index uint, state lexer, scan scanState) lean.FoldControl[lexer] {
	start := scan.Start
	word := classify(state.Source.Extract(start, index))
	if word.Kind == 0 {
		return lexError(state, InvalidLexeme, start)
	}
	words := state.Words.Push(lexeme{Kind: word.Kind, Value: word.Value, Offset: start})
	return lean.FoldControl[lexer]{State: lexer{Source: state.Source, Words: words, Scan: scan, Error: state.Error}, Stop: false}
}

func lexError(state lexer, kind DiagnosticKind, offset uint) lean.FoldControl[lexer] {
	return lean.FoldControl[lexer]{
		State: lexer{Source: state.Source, Words: state.Words, Scan: state.Scan, Error: Diagnostic{Kind: kind, Offset: offset}},
		Stop:  true,
	}
}

func tokenize(source lean.ByteArray) lexer {
	initial := lexer{Source: source, Words: lean.Array[lexeme]{}, Scan: scanState{Start: 0, InWord: false}, Error: noDiagnostic()}
	scanned := lean.FoldNUntil(source.Size(), initial, scanSourceByte)
	if scanned.Stop || !scanned.State.Scan.InWord {
		return scanned.State
	}
	return closeWord(source.Size(), scanned.State, scanState{Start: scanned.State.Scan.Start, InWord: false}).State
}

type expression struct {
	Word  lexeme
	Left  lean.Box[expression]
	Right lean.Box[expression]
}

func leaf(word lexeme) expression {
	return expression{Word: word, Left: lean.Box[expression]{}, Right: lean.Box[expression]{}}
}

func emptyExpression() expression {
	return leaf(lexeme{Kind: 0, Value: 0, Offset: 0})
}

type parser struct {
	Words lean.Array[lexeme]
	Roots lean.Array[expression]
}

func arity(kind byte) uint {
	if kind == integerToken || kind == booleanToken {
		return 0
	}
	if kind == notToken {
		return 1
	}
	return 2
}

func parseWord(index uint, state parser) lean.FoldControl[parser] {
	word := state.Words.Get(state.Words.Size() - 1 - index).UnwrapOr(lexeme{Kind: 0, Value: 0, Offset: 0})
	operands := arity(word.Kind)
	roots := state.Roots
	depth := roots.Size()
	if depth < operands {
		return lean.FoldControl[parser]{State: state, Stop: true}
	}
	if operands == 0 {
		return lean.FoldControl[parser]{State: parser{Words: state.Words, Roots: roots.Push(leaf(word))}, Stop: false}
	}
	left := roots.Get(depth - 1).UnwrapOr(emptyExpression())
	if operands == 1 {
		node := expression{Word: word, Left: lean.NewBox(left), Right: lean.Box[expression]{}}
		return lean.FoldControl[parser]{State: parser{Words: state.Words, Roots: roots.Pop().Push(node)}, Stop: false}
	}
	right := roots.Get(depth - 2).UnwrapOr(emptyExpression())
	node := expression{Word: word, Left: lean.NewBox(left), Right: lean.NewBox(right)}
	return lean.FoldControl[parser]{State: parser{Words: state.Words, Roots: roots.Pop().Pop().Push(node)}, Stop: false}
}

func parse(words lean.Array[lexeme]) lean.FoldControl[parser] {
	initial := parser{Words: words, Roots: lean.Array[expression]{}}
	return lean.FoldNUntil(words.Size(), initial, parseWord)
}

type signature struct {
	Operand Type
	Result  Type
}

func operatorTypes(kind byte) signature {
	if kind == addToken || kind == subToken {
		return signature{Operand: U8, Result: U8}
	}
	if kind == eqToken || kind == ltToken {
		return signature{Operand: U8, Result: Bool}
	}
	return signature{Operand: Bool, Result: Bool}
}

type typing struct {
	Type  Type
	Error Diagnostic
}

func typed(kind Type) typing {
	return typing{Type: kind, Error: noDiagnostic()}
}

func mismatch(offset uint) typing {
	return typing{Type: 0, Error: Diagnostic{Kind: TypeMismatch, Offset: offset}}
}

//golean:termination:by sizeOf expr
func checkExpression(expr expression) typing {
	word := expr.Word
	if word.Kind == integerToken {
		return typed(U8)
	}
	if word.Kind == booleanToken {
		return typed(Bool)
	}
	if !expr.Left.IsSome() {
		return mismatch(word.Offset)
	}
	if expr.Right.IsSome() {
		right := checkExpression(expr.Right.Get())
		if right.Error.Kind != NoDiagnostic {
			return right
		}
		left := checkExpression(expr.Left.Get())
		if left.Error.Kind != NoDiagnostic {
			return left
		}
		sig := operatorTypes(word.Kind)
		if left.Type != sig.Operand || right.Type != sig.Operand {
			return mismatch(word.Offset)
		}
		return typed(sig.Result)
	}
	operand := checkExpression(expr.Left.Get())
	if operand.Error.Kind != NoDiagnostic {
		return operand
	}
	if operand.Type != Bool {
		return mismatch(word.Offset)
	}
	return typed(Bool)
}

type instruction struct {
	Opcode  byte
	Operand byte
}

func encode(kind, value byte) instruction {
	if kind == integerToken || kind == booleanToken {
		return instruction{Opcode: Push, Operand: value}
	}
	return instruction{Opcode: kind - addToken + Add, Operand: 0}
}

func emitWord(word lexeme, code lean.ByteArray) lean.ByteArray {
	inst := encode(word.Kind, word.Value)
	return code.Push(inst.Opcode).Push(inst.Operand)
}

//golean:termination:by sizeOf expr
func emitExpression(expr expression, code lean.ByteArray) lean.ByteArray {
	if !expr.Left.IsSome() {
		return emitWord(expr.Word, code)
	}
	if expr.Right.IsSome() {
		right := emitExpression(expr.Right.Get(), code)
		left := emitExpression(expr.Left.Get(), right)
		return emitWord(expr.Word, left)
	}
	operand := emitExpression(expr.Left.Get(), code)
	return emitWord(expr.Word, operand)
}

func emit(expr expression) lean.ByteArray {
	return emitExpression(expr, lean.ByteArray{}).Push(Halt).Push(0)
}

type compilation struct {
	Code  lean.ByteArray
	Type  Type
	Error Diagnostic
}

func failed(d Diagnostic) compilation {
	return compilation{Code: lean.ByteArray{}, Type: 0, Error: d}
}

const maxEncodedNodes = (math.MaxInt - 2) / 2

func codeFits(nodes uint) bool { return nodes <= maxEncodedNodes }

//golean:export
func Compile(source lean.ByteArray) compilation {
	lexed := tokenize(source)
	if lexed.Error.Kind != NoDiagnostic {
		return failed(lexed.Error)
	}
	parsed := parse(lexed.Words)
	if parsed.Stop || parsed.State.Roots.Size() != 1 {
		return failed(Diagnostic{Kind: SyntaxError, Offset: source.Size()})
	}
	root := parsed.State.Roots.Get(0).UnwrapOr(emptyExpression())
	checked := checkExpression(root)
	if checked.Error.Kind != NoDiagnostic {
		return failed(checked.Error)
	}
	if !codeFits(lexed.Words.Size()) {
		return failed(Diagnostic{Kind: CodeTooLarge, Offset: source.Size()})
	}
	return compilation{Code: emit(root), Type: checked.Type, Error: noDiagnostic()}
}
