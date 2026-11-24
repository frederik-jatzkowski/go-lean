// Package compiler translates typed prefix expressions to stack bytecode.
package compiler

import (
	model "github.com/frederik-jatzkowski/go-lean/examples/proven/stack_machine_compiler/model"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

type Compiled struct {
	Code []byte
	Type model.Type
}

// Compile translates source or reports the first compiler diagnostic.
func Compile(source []byte) (Compiled, model.Diagnostic) {
	result := model.Compile(lean.ByteArrayFromBytes(source))
	if result.Error.Kind != model.NoDiagnostic {
		return Compiled{}, result.Error
	}
	compiled := Compiled{Code: make([]byte, result.Code.Size()), Type: result.Type}
	for i := range compiled.Code {
		compiled.Code[i] = result.Code.Get(uint(i)).UnwrapOr(0)
	}
	return compiled, model.Diagnostic{}
}
