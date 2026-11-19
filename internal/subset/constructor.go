package subset

import (
	"go/token"
	"go/types"

	"golang.org/x/tools/go/ssa"
)

func (c *checker) checkConstructor(fn *ssa.Function) error {
	record := fn.Signature.Results().At(0).Type().Underlying().(*types.Struct)
	for field := range record.Fields() {
		if interfaceRecord(field.Type()) {
			return diagnostic(fn, field.Pos(), "verified constructors require annotated interface fields directly on the returned struct")
		}
	}
	for _, block := range fn.Blocks {
		for _, instruction := range block.Instrs {
			switch ins := instruction.(type) {
			case *ssa.Return:
				continue
			case *ssa.BinOp:
				if ins.Op != token.QUO && ins.Op != token.REM {
					continue
				}
				return diagnostic(fn, ins.Pos(), "division and remainder are unsupported in verified constructors")
			default:
				if constructorInstruction(instruction) {
					continue
				}
				return diagnostic(fn, instruction.Pos(), "unsupported verified constructor instruction %T", instruction)
			}
		}
	}
	return nil
}

func (c *checker) checkConstructorReturn(fn *ssa.Function, ret *ssa.Return) error {
	if load, ok := ret.Results[0].(*ssa.UnOp); ok && load.Op == token.MUL {
		if alloc, ok := load.X.(*ssa.Alloc); ok && c.records[alloc].Fields != nil {
			return nil
		}
	}
	return diagnostic(fn, ret.Pos(), "constructor must return a struct with every interface field initialized on every path")
}

func constructorInstruction(ins ssa.Instruction) bool {
	switch ins := ins.(type) {
	case *ssa.Alloc, *ssa.Store, *ssa.FieldAddr, *ssa.Field, *ssa.If, *ssa.Jump, *ssa.Phi, *ssa.Convert, *ssa.ChangeType:
		return true
	case *ssa.UnOp:
		if ins.Op != token.MUL {
			return true
		}
		_, alloc := recordAddressBase(ins.X).(*ssa.Alloc)
		return alloc
	default:
		return false
	}
}
