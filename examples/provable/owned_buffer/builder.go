package owned_buffer

type Instruction struct {
	Opcode uint8
	Target uint16
}

type Builder struct {
	code    []Instruction
	offsets []int
	input   []uint16
	cursor  int
}

func planJump(opcode uint8) Instruction {
	return Instruction{Opcode: opcode}
}

func (b *Builder) emit(inst Instruction) int {
	index := len(b.code)
	b.code = append(b.code, inst)
	return index
}

func (b *Builder) patch(index int, target uint16) {
	b.code[index].Target = target
}

func (b *Builder) note(index int) {
	b.offsets = append(b.offsets, index)
}

// Build emits a placeholder for each target and patches its destination.
//
//golean:verify appendReturnsIndex : ∀ (before : Builder) (inst : Instruction),
//golean:verify+   let code := before.«field:code».getD #[]
//golean:verify+   «Builder$emit» (some before) inst =
//golean:verify+     some (some { before with «field:code» := some (code.push inst) }, .ofNat code.size) ∧
//golean:verify+   (code.push inst)[code.size]? = some inst
//golean:verify patchPreservesOffsets : ∀ (before : Builder) (index : GoTypes.Int) (target : UInt16) (old : Instruction),
//golean:verify+   0 ≤ index.toInt → (before.«field:code».getD #[])[index.toNatClampNeg]? = some old →
//golean:verify+   ∃ after, «Builder$patch» (some before) index target = some (some after, ()) ∧
//golean:verify+     after.«field:offsets» = before.«field:offsets» ∧
//golean:verify+     (after.«field:code».getD #[])[index.toNatClampNeg]? = some { old with «field:Target» := target }
//golean:verify buildsThree : let result := «Builder$Build» (some ⟨none, none, none, 0⟩) (some (List.replicate 3 42));
//golean:verify+   (result.bind fun output => output.1.map fun builder =>
//golean:verify+     let code := builder.«field:code».getD #[]
//golean:verify+     let offsets := builder.«field:offsets».getD #[]
//golean:verify+     (code.size, offsets.size, offsets[2]?, code.all (fun inst => inst.«field:Opcode» == 1 && inst.«field:Target» == 42))) =
//golean:verify+     some (3, 3, some 2, true)
func (b *Builder) Build(targets []uint16) {
	b.input = targets
	b.code = make([]Instruction, 0, 4*len(targets))
	b.offsets = make([]int, 0, len(targets))
	b.cursor = 0
	for b.cursor < len(b.input) {
		target := b.input[b.cursor]
		index := b.emit(planJump(1))
		b.note(index)
		b.patch(index, target)
		b.cursor++
	}
}
