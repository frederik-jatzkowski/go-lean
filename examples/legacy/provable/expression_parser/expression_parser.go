//golean:verify:import expression_parser.expression_rules
package expression_parser

type TokenKind uint8

const (
	Number TokenKind = iota + 1
	Plus
	Minus
)

//golean:verify tokenizes : ∀ input : ExpressionRules.Bytes,
//golean:verify+   let xs := ExpressionRules.contents input
//golean:verify+   let lexed := ExpressionRules.lex false xs
//golean:verify+   Tokenize input = (some (lexed.1, xs.length), lexed.2)
func Tokenize(input []byte) ([]TokenKind, bool) {
	out := make([]TokenKind, 0, len(input))
	valid, inNumber := true, false
	for _, b := range input {
		var token TokenKind
		if valid {
			if '0' <= b && b <= '9' {
				if !inNumber {
					token = Number
				}
				inNumber = true
			} else if b == '+' {
				token = Plus
				inNumber = false
			} else if b == '-' {
				token = Minus
				inNumber = false
			} else {
				valid = false
			}
		}
		if token != 0 {
			out = append(out, token)
		}
	}
	return out, valid
}

//golean:verify parses : ∀ tokens : ExpressionRules.Bytes,
//golean:verify+   Parse tokens = ExpressionRules.tokenGrammar true (ExpressionRules.contents tokens)
func Parse(tokens []TokenKind) bool {
	const needNumber, afterNumber, invalid uint8 = 0, 1, 2
	state := needNumber
	for _, token := range tokens {
		if state != invalid {
			if state == needNumber && token == Number {
				state = afterNumber
			} else if state == afterNumber && (token == Plus || token == Minus) {
				state = needNumber
			} else {
				state = invalid
			}
		}
	}
	return state == afterNumber
}

//golean:verify recognizes : ∀ input : ExpressionRules.Bytes,
//golean:verify+   Recognize input = ExpressionRules.byteGrammar true (ExpressionRules.contents input)
func Recognize(input []byte) bool {
	tokens, ok := Tokenize(input)
	return ok && Parse(tokens)
}
