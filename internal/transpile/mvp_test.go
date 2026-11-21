package transpile_test

import (
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

const collectionSource = `func collect(keys []string) ([]string, map[string]int) {
	out := make([]string, 0, len(keys))
	counts := make(map[string]int)
	for _, key := range keys {
		if key == "" {
			continue
		}
		out = append(out, key)
		counts[key]++
	}
	return out, counts
}
`

func TestMVPTranslations(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

type invalid struct{}
func (invalid) Error() string { return "invalid" }

func cut(s string, low int, high uint) (string, error) {
	if s == "" {
		return "", invalid{}
	}
	return s[low:high], nil
}

//golean:export
func forward(s string, low int, high uint) (string, error, bool) {
	value, err := cut(s, low, high)
	return value, err, err == nil
}

//golean:export
func casts(s int8, u uint64, n int64) (uint64, int64, uint8) {
	return uint64(s), int64(u), uint8(n)
}

//golean:export
func choose(x, y, divisor int32) int32 {
	return min(max(x), y, 10/divisor)
}

`+collectionSource+`
//golean:export
func summarize(keys []string, target string) (int, int, int, bool) {
	out, counts := collect(keys)
	value, ok := counts[target]
	return len(out), cap(out), value, ok
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	checkGeneratedLean(t, dir, outputs[0].Path, outputs[0].Source, `
open GoLean.«example.test/sample».input
private def invalidByte : ByteArray := ByteArray.mk #[255]
private def emptyByte : ByteArray := ByteArray.mk #[]
example : forward (ByteArray.mk #[120, 255, 0]) 1 3 =
    some (ByteArray.mk #[255, 0], none, true) := by decide
example : forward emptyByte 0 0 = some (emptyByte, some "example.test/sample.invalid", false) := by decide
example : forward invalidByte (-1) 1 = none := by decide
example : forward invalidByte 1 0 = none := by decide
example : forward invalidByte 0 2 = none := by decide
example : casts (-1) 18446744073709551615 (-257) = (18446744073709551615, -1, 255) := by decide
example : choose (-5) 8 2 = some (-5) := by decide
example : choose 9 7 2 = some 5 := by decide
example : choose 9 7 0 = none := by decide
example : summarize none invalidByte = (0, 0, 0, false) := by decide
example : summarize (some ([], 5)) invalidByte = (0, 0, 0, false) := by decide
example : summarize (some ([emptyByte, emptyByte], 3)) emptyByte = (0, 2, 0, false) := by decide
example : summarize (some ([invalidByte, emptyByte, invalidByte, invalidByte], 7)) invalidByte = (3, 4, 3, true) := by decide
`)
}

func TestCollectionFoldRejectsUnownedOrLargerAppends(t *testing.T) {
	for _, test := range []struct {
		name, old, replacement, extra, want string
	}{
		{"escape", "counts[key]++", "counts[key]++; saved = counts", "var saved map[string]int", "cannot write collection after publication"},
		{"caller write", "counts[key]++", "counts[key]++; keys[0] = key", "", "slice elements are read-only"},
		{"multiple appended values", "append(out, key)", "append(out, []string{0: key, 1: \"\"}...)", "", "local array address must not escape"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			source := strings.Replace(collectionSource, test.old, test.replacement, 1)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n//golean:export\n"+source+test.extra+"\n")
			if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("expected %q, got %v", test.want, err)
			}
		})
	}
}
