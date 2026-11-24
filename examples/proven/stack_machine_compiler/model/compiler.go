// Package compiler translates typed prefix expressions to stack bytecode.
//
//golean:generate:enum Lexeme { MissingLexeme default, IntegerLexeme, BooleanLexeme, AddLexeme, SubLexeme, EqLexeme, LtLexeme, AndLexeme, NotLexeme }
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

type MissingLexeme struct{}

type IntegerLexeme struct {
	Offset uint
	Value  byte
}

type BooleanLexeme struct {
	Offset uint
	Value  bool
}

type AddLexeme struct{ Offset uint }

type SubLexeme struct{ Offset uint }

type EqLexeme struct{ Offset uint }

type LtLexeme struct{ Offset uint }

type AndLexeme struct{ Offset uint }

type NotLexeme struct{ Offset uint }

func missingLexeme(word Lexeme) bool {
	switch word.Case().(type) {
	case MissingLexeme:
		return true
	case IntegerLexeme:
		return false
	case BooleanLexeme:
		return false
	case AddLexeme:
		return false
	case SubLexeme:
		return false
	case EqLexeme:
		return false
	case LtLexeme:
		return false
	case AndLexeme:
		return false
	case NotLexeme:
		return false
	}
	return false
}

func lexemeOffset(word Lexeme) uint {
	switch token := word.Case().(type) {
	case MissingLexeme:
		return 0
	case IntegerLexeme:
		return token.Offset
	case BooleanLexeme:
		return token.Offset
	case AddLexeme:
		return token.Offset
	case SubLexeme:
		return token.Offset
	case EqLexeme:
		return token.Offset
	case LtLexeme:
		return token.Offset
	case AndLexeme:
		return token.Offset
	case NotLexeme:
		return token.Offset
	}
	return 0
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

func timesTen(n byte) byte {
	twice := n + n
	four := twice + twice
	return four + four + twice
}

func decimal(a, b, c byte, width uint) lean.Option[byte] {
	invalid := lean.None[byte]()
	if !isDigit(a) {
		return invalid
	}
	if width == 1 {
		return lean.Some(a - '0')
	}
	if a == '0' || !isDigit(b) {
		return invalid
	}
	prefix := timesTen(a-'0') + (b - '0')
	if width == 2 {
		return lean.Some(prefix)
	}
	if width != 3 || !isDigit(c) {
		return invalid
	}
	if a > '2' || (a == '2' && (b > '5' || (b == '5' && c > '5'))) {
		return invalid
	}
	return lean.Some(timesTen(prefix) + (c - '0'))
}

func classify(source lean.ByteArray, offset uint) Lexeme {
	width := source.Size()
	a := source.Get(0).UnwrapOr(0)
	b := source.Get(1).UnwrapOr(0)
	c := source.Get(2).UnwrapOr(0)
	if width == 2 {
		if a == 'e' && b == 'q' {
			return NewLexemeEqLexeme(EqLexeme{Offset: offset})
		}
		if a == 'l' && b == 't' {
			return NewLexemeLtLexeme(LtLexeme{Offset: offset})
		}
	}
	if width == 3 {
		if a == 'a' && b == 'd' && c == 'd' {
			return NewLexemeAddLexeme(AddLexeme{Offset: offset})
		}
		if a == 's' && b == 'u' && c == 'b' {
			return NewLexemeSubLexeme(SubLexeme{Offset: offset})
		}
		if a == 'a' && b == 'n' && c == 'd' {
			return NewLexemeAndLexeme(AndLexeme{Offset: offset})
		}
		if a == 'n' && b == 'o' && c == 't' {
			return NewLexemeNotLexeme(NotLexeme{Offset: offset})
		}
	}
	if width == 4 && a == 't' && b == 'r' && c == 'u' && source.Get(3).UnwrapOr(0) == 'e' {
		return NewLexemeBooleanLexeme(BooleanLexeme{Offset: offset, Value: true})
	}
	if width == 5 && a == 'f' && b == 'a' && c == 'l' &&
		source.Get(3).UnwrapOr(0) == 's' && source.Get(4).UnwrapOr(0) == 'e' {
		return NewLexemeBooleanLexeme(BooleanLexeme{Offset: offset, Value: false})
	}
	return decimalLexeme(a, b, c, width, offset)
}

func decimalLexeme(a, b, c byte, width, offset uint) Lexeme {
	number := decimal(a, b, c, width)
	if number.IsSome() {
		return NewLexemeIntegerLexeme(IntegerLexeme{Offset: offset, Value: number.UnwrapOr(0)})
	}
	return Lexeme{}
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
	Words  lean.Array[Lexeme]
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
	word := classify(state.Source.Extract(start, index), start)
	if missingLexeme(word) {
		return lexError(state, InvalidLexeme, start)
	}
	words := state.Words.Push(word)
	return lean.FoldControl[lexer]{State: lexer{Source: state.Source, Words: words, Scan: scan, Error: state.Error}, Stop: false}
}

func lexError(state lexer, kind DiagnosticKind, offset uint) lean.FoldControl[lexer] {
	return lean.FoldControl[lexer]{
		State: lexer{Source: state.Source, Words: state.Words, Scan: state.Scan, Error: Diagnostic{Kind: kind, Offset: offset}},
		Stop:  true,
	}
}

func tokenize(source lean.ByteArray) lexer {
	initial := lexer{Source: source, Words: lean.Array[Lexeme]{}, Scan: scanState{Start: 0, InWord: false}, Error: noDiagnostic()}
	scanned := lean.FoldNUntil(source.Size(), initial, scanSourceByte)
	if scanned.Stop || !scanned.State.Scan.InWord {
		return scanned.State
	}
	return closeWord(source.Size(), scanned.State, scanState{Start: scanned.State.Scan.Start, InWord: false}).State
}

type expression struct {
	Word  Lexeme
	Left  lean.Box[expression]
	Right lean.Box[expression]
}

func leaf(word Lexeme) expression {
	return expression{Word: word, Left: lean.Box[expression]{}, Right: lean.Box[expression]{}}
}

func emptyExpression() expression {
	return leaf(Lexeme{})
}

type parser struct {
	Words lean.Array[Lexeme]
	Roots lean.Array[expression]
}

func arity(word Lexeme) uint {
	switch word.Case().(type) {
	case MissingLexeme:
		return 2
	case IntegerLexeme:
		return 0
	case BooleanLexeme:
		return 0
	case AddLexeme:
		return 2
	case SubLexeme:
		return 2
	case EqLexeme:
		return 2
	case LtLexeme:
		return 2
	case AndLexeme:
		return 2
	case NotLexeme:
		return 1
	}
	return 2
}

func parseWord(index uint, state parser) lean.FoldControl[parser] {
	word := state.Words.Get(state.Words.Size() - 1 - index).UnwrapOr(Lexeme{})
	operands := arity(word)
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

func parse(words lean.Array[Lexeme]) lean.FoldControl[parser] {
	initial := parser{Words: words, Roots: lean.Array[expression]{}}
	return lean.FoldNUntil(words.Size(), initial, parseWord)
}

type signature struct {
	Operand Type
	Result  Type
}

func operatorTypes(word Lexeme) signature {
	switch word.Case().(type) {
	case MissingLexeme:
		return signature{Operand: Bool, Result: Bool}
	case IntegerLexeme:
		return signature{Operand: Bool, Result: Bool}
	case BooleanLexeme:
		return signature{Operand: Bool, Result: Bool}
	case AddLexeme:
		return signature{Operand: U8, Result: U8}
	case SubLexeme:
		return signature{Operand: U8, Result: U8}
	case EqLexeme:
		return signature{Operand: U8, Result: Bool}
	case LtLexeme:
		return signature{Operand: U8, Result: Bool}
	case AndLexeme:
		return signature{Operand: Bool, Result: Bool}
	case NotLexeme:
		return signature{Operand: Bool, Result: Bool}
	}
	return signature{Operand: Bool, Result: Bool}
}

func literalType(word Lexeme) Type {
	switch word.Case().(type) {
	case MissingLexeme:
		return 0
	case IntegerLexeme:
		return U8
	case BooleanLexeme:
		return Bool
	case AddLexeme:
		return 0
	case SubLexeme:
		return 0
	case EqLexeme:
		return 0
	case LtLexeme:
		return 0
	case AndLexeme:
		return 0
	case NotLexeme:
		return 0
	}
	return 0
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
	literal := literalType(word)
	if literal != 0 {
		return typed(literal)
	}
	if !expr.Left.IsSome() {
		return mismatch(lexemeOffset(word))
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
		sig := operatorTypes(word)
		if left.Type != sig.Operand || right.Type != sig.Operand {
			return mismatch(lexemeOffset(word))
		}
		return typed(sig.Result)
	}
	operand := checkExpression(expr.Left.Get())
	if operand.Error.Kind != NoDiagnostic {
		return operand
	}
	if operand.Type != Bool {
		return mismatch(lexemeOffset(word))
	}
	return typed(Bool)
}

func emitWord(word Lexeme, code lean.ByteArray) lean.ByteArray {
	switch token := word.Case().(type) {
	case MissingLexeme:
		return code.Push(255).Push(0)
	case IntegerLexeme:
		return code.Push(Push).Push(token.Value)
	case BooleanLexeme:
		if token.Value {
			return code.Push(Push).Push(1)
		}
		return code.Push(Push).Push(0)
	case AddLexeme:
		return code.Push(Add).Push(0)
	case SubLexeme:
		return code.Push(Sub).Push(0)
	case EqLexeme:
		return code.Push(Eq).Push(0)
	case LtLexeme:
		return code.Push(Lt).Push(0)
	case AndLexeme:
		return code.Push(And).Push(0)
	case NotLexeme:
		return code.Push(Not).Push(0)
	}
	return code
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
