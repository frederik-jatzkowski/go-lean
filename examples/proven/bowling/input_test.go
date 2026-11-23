package bowling

import (
	"slices"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func TestPlay(t *testing.T) {
	perfect := strings.Repeat("10,", 11) + "10"
	gutters := strings.Repeat("0,", 18)
	tests := []struct {
		name     string
		input    string
		accepted int
		rejected []int
		score    int
		complete bool
	}{
		{name: "empty"},
		{name: "whitespace", input: " \t\r\n"},
		{name: "strike and two deliveries", input: "\t10, 3,\r\n4 ", accepted: 3},
		{name: "one at EOF", input: "1", accepted: 1},
		{name: "rejected delivery keeps the rack", input: "8, 5, 2", accepted: 2, rejected: []int{1}},
		{name: "perfect", input: perfect, accepted: 12, score: 300, complete: true},
		{name: "tenth-frame spare", input: gutters + "7,3,10", accepted: 21, score: 20, complete: true},
		{name: "extra delivery", input: perfect + ",0", accepted: 12, rejected: []int{12}, score: 300, complete: true},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			result, ok := playBytes([]byte(test.input))
			if !ok {
				t.Fatalf("Play(%q) rejected valid syntax", test.input)
			}
			want := make([]bool, test.accepted+len(test.rejected))
			for i := range want {
				want[i] = !slices.Contains(test.rejected, i)
			}
			got := lean.FoldList(result.Decisions(), []bool(nil), func(accepted bool, trace []bool) []bool {
				return append(trace, accepted)
			})
			if !slices.Equal(got, want) {
				t.Fatalf("acceptance trace = %v, want %v", got, want)
			}
			if score, complete := scoreGame(result.Game()); score != test.score || complete != test.complete {
				t.Fatalf("Score() = (%d, %t), want (%d, %t)", score, complete, test.score, test.complete)
			}
		})
	}
}

func TestPlayRejectsMalformedInput(t *testing.T) {
	for _, input := range []string{
		"01", "11", "100", "1 0", "1 2", "1,,2", "1,", ",1", ",",
		"-1", "+1", "é", "\x00", "1\v,2", "10,3,\xff",
	} {
		if result, ok := playBytes([]byte(input)); ok || result != (replayResult{}) {
			t.Errorf("Play(%q) should reject syntax and return the zero result", input)
		}
	}
}

func playBytes(input []byte) (replayResult, bool) {
	result := Play(lean.ByteArrayFromBytes(input))
	return result.UnwrapOr(replayResult{}), result.IsSome()
}
