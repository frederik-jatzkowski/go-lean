// Package compiler translates typed prefix expressions to stack bytecode.
//
//golean:verify:import bytecode_vm.compiler.compiler_contract
package compiler

const (
	MaxSourceBytes = 256
	MaxTokens      = 32
	CodeSize       = 2 * (MaxTokens + 1)
)

type Type uint8

const (
	U8 Type = iota + 1
	Bool
)

type DiagnosticKind uint8

const (
	NoDiagnostic DiagnosticKind = iota
	SourceTooLong
	InvalidLexeme
	TooManyTokens
	SyntaxError
	TypeMismatch
)

type Diagnostic struct {
	Kind   DiagnosticKind
	Offset uint16
}

type Compiled struct {
	Code    [CodeSize]byte
	CodeLen uint8
	Type    Type
}

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

type tokens struct {
	Kind  [MaxTokens]byte
	Value [MaxTokens]byte
	Start [MaxTokens]uint16
	Count uint8
	End   uint16
}

func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func isDigit(b byte) bool {
	return b >= '0' && b <= '9'
}

func matchPair(a, b, first, second byte) bool {
	return a == first && b == second
}

func matchTriple(a, b, c, first, second, third byte) bool {
	return matchPair(a, b, first, second) && c == third
}

func classifyTwo(a, b byte) (byte, byte) {
	switch {
	case matchPair(a, b, 'e', 'q'):
		return eqToken, 0
	case matchPair(a, b, 'l', 't'):
		return ltToken, 0
	case a != '0' && isDigit(a) && isDigit(b):
		return integerToken, 10*(a-'0') + (b - '0')
	default:
		return 0, 0
	}
}

func classifyThree(a, b, c byte) (byte, byte) {
	switch {
	case matchTriple(a, b, c, 'a', 'd', 'd'):
		return addToken, 0
	case matchTriple(a, b, c, 's', 'u', 'b'):
		return subToken, 0
	case matchTriple(a, b, c, 'a', 'n', 'd'):
		return andToken, 0
	case matchTriple(a, b, c, 'n', 'o', 't'):
		return notToken, 0
	case a != '0' && isDigit(a) && isDigit(b) && isDigit(c):
		number := 100*uint16(a-'0') + 10*uint16(b-'0') + uint16(c-'0')
		if number <= 255 {
			return integerToken, byte(number)
		}
	}
	return 0, 0
}

func classify(source []byte, start, width int) (byte, byte) {
	switch width {
	case 1:
		a := source[start]
		if isDigit(a) {
			return integerToken, a - '0'
		}
	case 2:
		return classifyTwo(source[start], source[start+1])
	case 3:
		return classifyThree(source[start], source[start+1], source[start+2])
	case 4:
		if matchPair(source[start], source[start+1], 't', 'r') &&
			matchPair(source[start+2], source[start+3], 'u', 'e') {
			return booleanToken, 1
		}
	case 5:
		if matchPair(source[start], source[start+1], 'f', 'a') &&
			matchTriple(source[start+2], source[start+3], source[start+4], 'l', 's', 'e') {
			return booleanToken, 0
		}
	}
	return 0, 0
}

//golean:verify tokenizerAgreement : LexerModel.Agrees
func tokenize(source []byte) (tokens, Diagnostic) {
	end := len(source)
	if end > MaxSourceBytes {
		return tokens{}, Diagnostic{Kind: SourceTooLong, Offset: MaxSourceBytes}
	}
	var kinds [MaxTokens]byte
	var values [MaxTokens]byte
	var offsets [MaxTokens]uint16
	count, start, width := 0, 0, 0
	limit := end + 1
	for i := 0; i < limit; i++ {
		if i < end && !isSpace(source[i]) {
			if width == 0 {
				start = i
			}
			width++
			continue
		}
		if width == 0 {
			continue
		}
		kind, value := classify(source, start, width)
		if kind == 0 {
			return tokens{}, Diagnostic{Kind: InvalidLexeme, Offset: uint16(start)}
		}
		if count == MaxTokens {
			return tokens{}, Diagnostic{Kind: TooManyTokens, Offset: uint16(start)}
		}
		kinds[count] = kind
		values[count] = value
		offsets[count] = uint16(start)
		count++
		width = 0
	}
	return tokens{Kind: kinds, Value: values, Start: offsets, Count: uint8(count), End: uint16(end)}, Diagnostic{}
}

type tree struct {
	Kind  [MaxTokens]byte
	Value [MaxTokens]byte
	Start [MaxTokens]uint16
	Left  [MaxTokens]uint8
	Right [MaxTokens]uint8
	Count uint8
}

type types struct {
	Nodes [MaxTokens]Type
	Root  Type
}

func arity(kind byte) int {
	if kind == integerToken || kind == booleanToken {
		return 0
	}
	if kind == notToken {
		return 1
	}
	return 2
}

//golean:verify parserAgreement : Parser.Contract
func parse(input tokens) (tree, Diagnostic) {
	count := int(input.Count)
	if count > MaxTokens {
		return tree{}, Diagnostic{Kind: SyntaxError, Offset: input.End}
	}
	var kinds, values [MaxTokens]byte
	var offsets [MaxTokens]uint16
	var left, right, roots [MaxTokens]uint8
	depth := 0
	for i := 0; i < count; i++ {
		sourceIndex := count - 1 - i
		kind := input.Kind[sourceIndex]
		operands := arity(kind)
		if depth < operands {
			return tree{}, Diagnostic{Kind: SyntaxError, Offset: input.End}
		}
		if operands >= 1 {
			depth--
			left[i] = roots[depth]
		}
		if operands == 2 {
			depth--
			right[i] = roots[depth]
		}
		kinds[i] = kind
		values[i] = input.Value[sourceIndex]
		offsets[i] = input.Start[sourceIndex]
		roots[depth] = uint8(i)
		depth++
	}
	if depth != 1 {
		return tree{}, Diagnostic{Kind: SyntaxError, Offset: input.End}
	}
	return tree{Kind: kinds, Value: values, Start: offsets, Left: left, Right: right, Count: input.Count}, Diagnostic{}
}

func operatorTypes(kind byte) (Type, Type) {
	switch kind {
	case addToken, subToken:
		return U8, U8
	case eqToken, ltToken:
		return U8, Bool
	default:
		return Bool, Bool
	}
}

func infer(kind byte, left, right, index int, inferred [MaxTokens]Type) Type {
	switch kind {
	case integerToken:
		return U8
	case booleanToken:
		return Bool
	}
	operand, result := operatorTypes(kind)
	if left >= index || inferred[left] != operand ||
		(arity(kind) == 2 && (right >= index || inferred[right] != operand)) {
		return 0
	}
	return result
}

//golean:verify typeCheckerAgreement : PassModel.TypeContract
func checkTypes(input tree) (types, Diagnostic) {
	count := int(input.Count)
	if count == 0 || count > MaxTokens {
		return types{}, Diagnostic{Kind: TypeMismatch}
	}
	var inferred [MaxTokens]Type
	for i := 0; i < count; i++ {
		nodeType := infer(input.Kind[i], int(input.Left[i]), int(input.Right[i]), i, inferred)
		if nodeType == 0 {
			return types{}, Diagnostic{Kind: TypeMismatch, Offset: input.Start[i]}
		}
		inferred[i] = nodeType
	}
	return types{Nodes: inferred, Root: inferred[count-1]}, Diagnostic{}
}

func encode(kind, value byte) (byte, byte) {
	if kind == integerToken || kind == booleanToken {
		return Push, value
	}
	return kind - addToken + Add, 0
}

//golean:verify emitterAgreement : PassModel.EmitContract
func emit(input tree) ([CodeSize]byte, uint8) {
	var code [CodeSize]byte
	count := int(input.Count)
	if count > MaxTokens {
		return code, 0
	}
	for i := 0; i < count; i++ {
		opcode, operand := encode(input.Kind[i], input.Value[i])
		code[2*i] = opcode
		code[2*i+1] = operand
	}
	// The next zero pair is Halt.
	return code, uint8(2 * (count + 1))
}

// Compile translates source or reports the first compiler diagnostic.
//
//golean:verify compilerAgreement : Pipeline.Contract
func Compile(source []byte) (Compiled, Diagnostic) {
	words, diagnostic := tokenize(source)
	if diagnostic.Kind != NoDiagnostic {
		return Compiled{}, diagnostic
	}
	syntax, diagnostic := parse(words)
	if diagnostic.Kind != NoDiagnostic {
		return Compiled{}, diagnostic
	}
	inferred, diagnostic := checkTypes(syntax)
	if diagnostic.Kind != NoDiagnostic {
		return Compiled{}, diagnostic
	}
	code, length := emit(syntax)
	return Compiled{Code: code, CodeLen: length, Type: inferred.Root}, Diagnostic{}
}
