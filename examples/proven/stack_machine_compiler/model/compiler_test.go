package compiler

import (
	"math"
	"testing"
)

func TestCodeFits(t *testing.T) {
	const last = (math.MaxInt - 2) / 2
	if !codeFits(last) || codeFits(last+1) || codeFits(^uint(0)) {
		t.Fatal("incorrect output-size boundary")
	}
}
