// Package compiler translates typed prefix expressions to stack bytecode.
//
//golean:verify:import spec
//golean:verify all : let observe := fun result : machineResult =>
//golean:verify+     let state := result.«field:state»
//golean:verify+     (result.«field:status», StackMachineCompiler.Spec.State.mk
//golean:verify+       state.«field:pc».toNat state.«field:stack»)
//golean:verify+   StackMachineCompiler.Spec.Requirements.all
//golean:verify+     (fun source =>
//golean:verify+       let result := compile source
//golean:verify+       let err := result.«field:diagnostic»
//golean:verify+       ⟨result.«field:code», result.«field:typeCode», err.«field:kind», err.«field:offset».toNat⟩)
//golean:verify+     (fun code pc stack aligned => observe (step code ⟨pc, stack⟩ aligned))
//golean:verify+     (fun code => observe (runCode code))
package compiler

import (
	"math"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

const (
	U8 uint8 = iota + 1
	Bool
)

const (
	NoDiagnostic uint8 = iota
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
	kind   byte
	value  byte
	offset uint
}

type diagnostic struct {
	kind   uint8
	offset uint
}

func noDiagnostic() diagnostic {
	return diagnostic{kind: NoDiagnostic, offset: 0}
}

func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

type classification struct {
	kind  byte
	value byte
}

func timesTen(n byte) byte {
	twice := n + n
	four := twice + twice
	return four + four + twice
}

func decimal(a, b, c byte, width uint) classification {
	invalid := classification{kind: 0, value: 0}
	if !isDigit(a) {
		return invalid
	}
	if width == 1 {
		return classification{kind: integerToken, value: a - '0'}
	}
	if a == '0' || !isDigit(b) {
		return invalid
	}
	prefix := timesTen(a-'0') + (b - '0')
	if width == 2 {
		return classification{kind: integerToken, value: prefix}
	}
	if width != 3 || !isDigit(c) {
		return invalid
	}
	if a > '2' || (a == '2' && (b > '5' || (b == '5' && c > '5'))) {
		return invalid
	}
	return classification{kind: integerToken, value: timesTen(prefix) + (c - '0')}
}

func classify(source lean.ByteArray) classification {
	width := source.Size()
	a := source.Get(0).UnwrapOr(0)
	b := source.Get(1).UnwrapOr(0)
	c := source.Get(2).UnwrapOr(0)
	if width == 2 {
		if a == 'e' && b == 'q' {
			return classification{kind: eqToken, value: 0}
		}
		if a == 'l' && b == 't' {
			return classification{kind: ltToken, value: 0}
		}
	}
	if width == 3 {
		if a == 'a' && b == 'd' && c == 'd' {
			return classification{kind: addToken, value: 0}
		}
		if a == 's' && b == 'u' && c == 'b' {
			return classification{kind: subToken, value: 0}
		}
		if a == 'a' && b == 'n' && c == 'd' {
			return classification{kind: andToken, value: 0}
		}
		if a == 'n' && b == 'o' && c == 't' {
			return classification{kind: notToken, value: 0}
		}
	}
	if width == 4 && a == 't' && b == 'r' && c == 'u' && source.Get(3).UnwrapOr(0) == 'e' {
		return classification{kind: booleanToken, value: 1}
	}
	if width == 5 && a == 'f' && b == 'a' && c == 'l' &&
		source.Get(3).UnwrapOr(0) == 's' && source.Get(4).UnwrapOr(0) == 'e' {
		return classification{kind: booleanToken, value: 0}
	}
	return decimal(a, b, c, width)
}

type scanState struct {
	start  uint
	inWord bool
}

type scanResult struct {
	state  scanState
	closed bool
}

func scanByte(state scanState, index uint, b byte) scanResult {
	if isSpace(b) {
		return scanResult{state: scanState{start: state.start, inWord: false}, closed: state.inWord}
	}
	if state.inWord {
		return scanResult{state: state, closed: false}
	}
	return scanResult{state: scanState{start: index, inWord: true}, closed: false}
}

type lexer struct {
	source     lean.ByteArray
	words      lean.Array[lexeme]
	scan       scanState
	diagnostic diagnostic
}

func scanSourceByte(index uint, state lexer) lean.FoldControl[lexer] {
	scanned := scanByte(state.scan, index, state.source.Get(index).UnwrapOr(' '))
	if !scanned.closed {
		return lean.FoldControl[lexer]{State: lexer{source: state.source, words: state.words, scan: scanned.state, diagnostic: state.diagnostic}, Stop: false}
	}
	return closeWord(index, state, scanned.state)
}

func closeWord(index uint, state lexer, scan scanState) lean.FoldControl[lexer] {
	start := scan.start
	word := classify(state.source.Extract(start, index))
	if word.kind == 0 {
		return lexError(state, InvalidLexeme, start)
	}
	words := state.words.Push(lexeme{kind: word.kind, value: word.value, offset: start})
	return lean.FoldControl[lexer]{State: lexer{source: state.source, words: words, scan: scan, diagnostic: state.diagnostic}, Stop: false}
}

func lexError(state lexer, kind uint8, offset uint) lean.FoldControl[lexer] {
	return lean.FoldControl[lexer]{
		State: lexer{source: state.source, words: state.words, scan: state.scan, diagnostic: diagnostic{kind: kind, offset: offset}},
		Stop:  true,
	}
}

func tokenize(source lean.ByteArray) lexer {
	initial := lexer{source: source, words: lean.Array[lexeme]{}, scan: scanState{start: 0, inWord: false}, diagnostic: noDiagnostic()}
	scanned := lean.FoldNUntil(source.Size(), initial, scanSourceByte)
	if scanned.Stop || !scanned.State.scan.inWord {
		return scanned.State
	}
	return closeWord(source.Size(), scanned.State, scanState{start: scanned.State.scan.start, inWord: false}).State
}

type expression struct {
	word  lexeme
	left  lean.Box[expression]
	right lean.Box[expression]
}

func leaf(word lexeme) expression {
	return expression{word: word, left: lean.Box[expression]{}, right: lean.Box[expression]{}}
}

func emptyExpression() expression {
	return leaf(lexeme{kind: 0, value: 0, offset: 0})
}

type parser struct {
	words lean.Array[lexeme]
	roots lean.Array[expression]
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
	word := state.words.Get(state.words.Size() - 1 - index).UnwrapOr(lexeme{kind: 0, value: 0, offset: 0})
	operands := arity(word.kind)
	roots := state.roots
	depth := roots.Size()
	if depth < operands {
		return lean.FoldControl[parser]{State: state, Stop: true}
	}
	if operands == 0 {
		return lean.FoldControl[parser]{State: parser{words: state.words, roots: roots.Push(leaf(word))}, Stop: false}
	}
	left := roots.Get(depth - 1).UnwrapOr(emptyExpression())
	if operands == 1 {
		node := expression{word: word, left: lean.NewBox(left), right: lean.Box[expression]{}}
		return lean.FoldControl[parser]{State: parser{words: state.words, roots: roots.Pop().Push(node)}, Stop: false}
	}
	right := roots.Get(depth - 2).UnwrapOr(emptyExpression())
	node := expression{word: word, left: lean.NewBox(left), right: lean.NewBox(right)}
	return lean.FoldControl[parser]{State: parser{words: state.words, roots: roots.Pop().Pop().Push(node)}, Stop: false}
}

func parse(words lean.Array[lexeme]) lean.FoldControl[parser] {
	initial := parser{words: words, roots: lean.Array[expression]{}}
	return lean.FoldNUntil(words.Size(), initial, parseWord)
}

type signature struct {
	operand uint8
	result  uint8
}

func operatorTypes(kind byte) signature {
	if kind == addToken || kind == subToken {
		return signature{operand: U8, result: U8}
	}
	if kind == eqToken || kind == ltToken {
		return signature{operand: U8, result: Bool}
	}
	return signature{operand: Bool, result: Bool}
}

type typing struct {
	typeCode   uint8
	diagnostic diagnostic
}

func typed(kind uint8) typing {
	return typing{typeCode: kind, diagnostic: noDiagnostic()}
}

func mismatch(offset uint) typing {
	return typing{typeCode: 0, diagnostic: diagnostic{kind: TypeMismatch, offset: offset}}
}

//golean:termination:by sizeOf expr
func checkExpression(expr expression) typing {
	word := expr.word
	if word.kind == integerToken {
		return typed(U8)
	}
	if word.kind == booleanToken {
		return typed(Bool)
	}
	if !expr.left.IsSome() {
		return mismatch(word.offset)
	}
	if expr.right.IsSome() {
		right := checkExpression(expr.right.Get())
		if right.diagnostic.kind != NoDiagnostic {
			return right
		}
		left := checkExpression(expr.left.Get())
		if left.diagnostic.kind != NoDiagnostic {
			return left
		}
		sig := operatorTypes(word.kind)
		if left.typeCode != sig.operand || right.typeCode != sig.operand {
			return mismatch(word.offset)
		}
		return typed(sig.result)
	}
	operand := checkExpression(expr.left.Get())
	if operand.diagnostic.kind != NoDiagnostic {
		return operand
	}
	if operand.typeCode != Bool {
		return mismatch(word.offset)
	}
	return typed(Bool)
}

type instruction struct {
	opcode  byte
	operand byte
}

func encode(kind, value byte) instruction {
	if kind == integerToken || kind == booleanToken {
		return instruction{opcode: Push, operand: value}
	}
	return instruction{opcode: kind - addToken + Add, operand: 0}
}

func emitWord(word lexeme, code lean.ByteArray) lean.ByteArray {
	inst := encode(word.kind, word.value)
	return code.Push(inst.opcode).Push(inst.operand)
}

//golean:termination:by sizeOf expr
func emitExpression(expr expression, code lean.ByteArray) lean.ByteArray {
	if !expr.left.IsSome() {
		return emitWord(expr.word, code)
	}
	if expr.right.IsSome() {
		right := emitExpression(expr.right.Get(), code)
		left := emitExpression(expr.left.Get(), right)
		return emitWord(expr.word, left)
	}
	operand := emitExpression(expr.left.Get(), code)
	return emitWord(expr.word, operand)
}

func emit(expr expression) lean.ByteArray {
	return emitExpression(expr, lean.ByteArray{}).Push(Halt).Push(0)
}

type compilation struct {
	code       lean.ByteArray
	typeCode   uint8
	diagnostic diagnostic
}

func failed(d diagnostic) compilation {
	return compilation{code: lean.ByteArray{}, typeCode: 0, diagnostic: d}
}

const maxEncodedNodes = (math.MaxInt - 2) / 2

func codeFits(nodes uint) bool { return nodes <= maxEncodedNodes }

//golean:export
func compile(source lean.ByteArray) compilation {
	lexed := tokenize(source)
	if lexed.diagnostic.kind != NoDiagnostic {
		return failed(lexed.diagnostic)
	}
	parsed := parse(lexed.words)
	if parsed.Stop || parsed.State.roots.Size() != 1 {
		return failed(diagnostic{kind: SyntaxError, offset: source.Size()})
	}
	root := parsed.State.roots.Get(0).UnwrapOr(emptyExpression())
	checked := checkExpression(root)
	if checked.diagnostic.kind != NoDiagnostic {
		return failed(checked.diagnostic)
	}
	if !codeFits(lexed.words.Size()) {
		return failed(diagnostic{kind: CodeTooLarge, offset: source.Size()})
	}
	return compilation{code: emit(root), typeCode: checked.typeCode, diagnostic: noDiagnostic()}
}

func CompileBytes(source lean.ByteArray) compilation { return compile(source) }
func (r compilation) Code() lean.ByteArray           { return r.code }
func (r compilation) Type() uint8                    { return r.typeCode }
func (r compilation) DiagnosticKind() uint8          { return r.diagnostic.kind }
func (r compilation) DiagnosticOffset() uint         { return r.diagnostic.offset }
