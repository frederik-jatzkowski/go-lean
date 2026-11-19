package transpile_test

import (
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func TestRecordSequenceFields(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample

type cells struct { values [2]int64 }
type board struct { cells cells; marker int64 }
type data struct { values []int64 }

//golean:export
func edit(flag bool, i int64) (board, board) {
	var original board
	updated := original
	updated.marker = 9
	updated.cells.values[i] = 3
	if flag { updated.cells.values[i] += 2 }
	updated.cells.values[1] = 7
	return original, updated
}

//golean:export
func unsigned(i uint8) int64 {
	var values [2]int64
	values[i] = 5
	return values[i]
}

//golean:export
func readBoard(b *board, i uint8) int64 { return b.cells.values[i] }

//golean:export
func initData(values []int64) data { return data{values: values} }

//golean:export
func emptyData() data { return data{values: []int64{}} }

//golean:export
func replace(d data, values []int64) (data, bool, int) {
	d.values = values
	return d, d.values == nil, len(d.values)
}

//golean:export
func read(d data, i uint8) int64 { return d.values[i] }

func copyValues(values []int64) []int64 {
	dst := make([]int64, len(values))
	copy(dst, values)
	return dst
}

//golean:export
func copyIntoField(values []int64) data { return initData(copyValues(values)) }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	if err := transpile.Write(outputs); err != nil {
		t.Fatal(err)
	}
	lake, err := exec.LookPath("lake")
	if err != nil {
		t.Skip("lake unavailable")
	}
	writeFile(t, filepath.Join(dir, "lakefile.toml"), `name = "RecordSequences"
defaultTargets = ["Checks"]
[[lean_lib]]
name = "Checks"
roots = ["input_gen", "checks"]
`)
	writeFile(t, filepath.Join(dir, "checks.lean"), `import input_gen
open GoLean.«example.test/sample».input

example : edit true 0 = some (⟨⟨#v[0, 0]⟩, 0⟩, ⟨⟨#v[5, 7]⟩, 9⟩) := rfl
example : edit false 0 = some (⟨⟨#v[0, 0]⟩, 0⟩, ⟨⟨#v[3, 7]⟩, 9⟩) := rfl
example : edit true (-1) = none := by decide
example : unsigned 1 = some 5 := by decide
example : unsigned 2 = none := by decide
example : readBoard (some ⟨⟨#v[7, 8]⟩, 0⟩) 1 = some 8 := rfl
example : readBoard none 1 = none := rfl
example : initData none = ⟨none⟩ := rfl
example : initData (some []) = ⟨some []⟩ := rfl
example : emptyData = ⟨some []⟩ := rfl
example : (replace (initData (some [])) none).2 = (true, 0) := rfl
example : (replace (initData none) (some [])).2 = (false, 0) := rfl
example : read (initData (some [11])) 0 = some 11 := rfl
example : read (initData none) 0 = none := rfl
example : copyIntoField none = some ⟨some []⟩ := rfl
`)
	checkLake(t, lake, dir, "")
}
