package expression_parser

import (
	"slices"
	"testing"
)

func TestExpression(t *testing.T) {
	for _, test := range []struct {
		input string
		ok    bool
	}{
		{"0", true}, {"001", true}, {"12+3-45", true},
		{"", false}, {"+1", false}, {"1-", false}, {"1++2", false},
		{"1 2", false}, {"1+é", false},
	} {
		if got := Recognize([]byte(test.input)); got != test.ok {
			t.Errorf("Recognize(%q) = %v, want %v", test.input, got, test.ok)
		}
	}
	if Recognize(nil) || Parse(nil) || Parse([]TokenKind{Number, 255, Number}) {
		t.Fatal("accepted empty input or an unknown token kind")
	}
}

func TestTokenize(t *testing.T) {
	for _, test := range []struct {
		input  []byte
		tokens []TokenKind
		ok     bool
	}{
		{nil, nil, true},
		{[]byte{}, nil, true},
		{[]byte("001"), []TokenKind{Number}, true},
		{[]byte("1++2"), []TokenKind{Number, Plus, Plus, Number}, true},
		{[]byte("12+x3"), []TokenKind{Number, Plus}, false},
	} {
		tokens, ok := Tokenize(test.input)
		if ok != test.ok || tokens == nil || cap(tokens) != len(test.input) || !slices.Equal(tokens, test.tokens) {
			t.Errorf("Tokenize(%q) = %v, %v, cap %d", test.input, tokens, ok, cap(tokens))
		}
	}
}
