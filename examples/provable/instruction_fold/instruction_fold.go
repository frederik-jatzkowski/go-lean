package instruction_fold

type Instruction struct {
	Operands []int64
}

func sumOperands(operands []int64, sum int64) int64 {
	for _, operand := range operands {
		sum += operand
	}
	return sum
}

func sumInstruction(ins Instruction, sum int64) int64 {
	for _, operand := range ins.Operands {
		sum += operand
	}
	return sum
}

//golean:verify byOperandsMatchesFlattenedFold : ∀ code : Option (List Instruction),
//golean:verify+   SumByOperands code = ((code.getD []).flatMap (fun ins => ins.«field:Operands».getD [])).foldl (· + ·) 0
func SumByOperands(code []Instruction) int64 {
	var sum int64
	for _, ins := range code {
		sum = sumOperands(ins.Operands, sum)
	}
	return sum
}

//golean:verify byInstructionMatchesFlattenedFold : ∀ code : Option (List Instruction),
//golean:verify+   SumByInstruction code = ((code.getD []).flatMap (fun ins => ins.«field:Operands».getD [])).foldl (· + ·) 0
func SumByInstruction(code []Instruction) int64 {
	var sum int64
	for _, ins := range code {
		sum = sumInstruction(ins, sum)
	}
	return sum
}
