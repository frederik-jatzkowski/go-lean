package transpile_test

import (
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestRejectOwnedBufferAliases(t *testing.T) {
	for _, test := range []struct {
		name, body, diagnostic string
	}{
		{"shared fields", "b.right = b.left; b.left[0] = 2; return nil", "owned buffer slice cannot escape"},
		{"escaping subslice", "b.left[0] = 2; return b.left[:1]", "owned buffer slice cannot escape"},
		{"stale slice", "old := b.left; b.left[0] = 2; return []int{old[0]}", "owned buffer slice cannot escape or be reused"},
		{"pending append", "pending := append(b.left, 2); b.left = append(b.left, 3); b.left = pending; return nil", "owned buffer append requires"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			path := filepath.Join(dir, "input.go")
			writeFile(t, path, "package sample\ntype Builder struct { left, right []int }\n"+
				"//golean:verify\nfunc (b *Builder) Run() []int {\nb.left = make([]int, 1, 4)\n"+test.body+"\n}\n")
			_, err := transpile.Generate(dir)
			if err == nil || !strings.Contains(err.Error(), test.diagnostic) {
				t.Fatalf("expected %q, got %v", test.diagnostic, err)
			}
		})
	}
}
