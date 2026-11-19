package lower

// newInputGraph creates a snapshot, independent of the original Go object graph.
func newInputGraph(program *sourceProgram) Input {
	graph := &inputGraph{ids: make(map[any]int64), phiBlocks: make(map[int64]int64),
		functionOrders: make(map[int64]int64), structuredLoops: make(map[int64]bool),
		callOwners: make(map[int64]int64), ordinaryOperands: make(map[int64]bool)}
	graph.encodeProgram(program)
	for i, fn := range program.Functions {
		graph.functionOrders[graph.ids[fn]] = int64(i)
		graph.indexCallOwners(fn)
	}
	for i, object := range graph.objects {
		if _, ok := object.(*sourceLoop); ok {
			graph.structuredLoops[int64(i)+1] = true
		}
		block, ok := object.(*sourceBlock)
		if !ok {
			continue
		}
		for _, ins := range block.Instructions {
			if len(ins.Operands) != 0 {
				graph.ordinaryOperands[graph.ids[ins]] = true
			}
			if ins.Kind == phiValue {
				graph.phiBlocks[graph.ids[ins]] = int64(i) + 1
			}
		}
	}
	graph.ids, graph.objects = nil, nil
	return graph
}

func (g *inputGraph) indexCallOwners(fn *sourceFunction) {
	seen := make(map[*sourceBlock]bool)
	pending := []*sourceBlock{fn.Entry}
	for len(pending) != 0 {
		block := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		if block == nil || seen[block] {
			continue
		}
		seen[block] = true
		for _, ins := range block.Instructions {
			if ins.Kind == callValue {
				g.callOwners[g.ids[ins]] = g.ids[fn]
			}
		}
		pending = append(pending, block.Succs...)
	}
}

func (g *inputGraph) row(id int64) *inputRow {
	if id <= 0 || id > int64(len(g.rows)) {
		return nil
	}
	return g.rows[id-1]
}
func (g *inputGraph) PackagePath() string  { return g.FieldText(1, fieldProgramPackage) }
func (g *inputGraph) FunctionCount() int64 { return g.ReferenceCount(1, fieldProgramFunctions) }
func (g *inputGraph) FunctionAt(position int64) int64 {
	return g.ReferenceAt(1, fieldProgramFunctions, position)
}
func (g *inputGraph) FunctionOrder(function int64) int64 {
	if order, exists := g.functionOrders[function]; exists {
		return order
	}
	return -1
}
func (g *inputGraph) HasRecord(id int64) bool { return g.row(id) != nil }
func (g *inputGraph) OrdinaryOperandCount(instruction int64) int64 {
	if !g.ordinaryOperands[instruction] {
		return 0
	}
	return g.ReferenceCount(instruction, fieldValueOperands)
}
func (g *inputGraph) OrdinaryOperandAt(instruction, position int64) int64 {
	if !g.ordinaryOperands[instruction] {
		return 0
	}
	operand := g.ReferenceAt(instruction, fieldValueOperands, position)
	return g.ReferenceAt(operand, fieldOperandValue, 0)
}
func (g *inputGraph) OperandDominates(instruction, position int64) bool {
	if !g.ordinaryOperands[instruction] {
		return false
	}
	operand := g.ReferenceAt(instruction, fieldValueOperands, position)
	return g.FieldNumber(operand, fieldOperandDominates) != 0
}
func (g *inputGraph) HasOrderedCall(call int64) bool {
	if owner := g.CallOwner(call); owner != 0 {
		target := g.CallTarget(call)
		return target != 0 && target != owner &&
			g.FieldNumber(g.ReferenceAt(call, fieldValueCall, 0), fieldCallClone) == 0
	}
	return false
}
func (g *inputGraph) CallTarget(call int64) int64 {
	if g.CallOwner(call) == 0 {
		return 0
	}
	return g.ReferenceAt(g.ReferenceAt(call, fieldValueCall, 0), fieldCallTarget, 0)
}
func (g *inputGraph) CallOwner(call int64) int64        { return g.callOwners[call] }
func (g *inputGraph) HasStructuredLoop(loop int64) bool { return g.structuredLoops[loop] }
func (g *inputGraph) LoopStateCount(loop int64) int64   { return g.ReferenceCount(loop, fieldLoopStates) }
func (g *inputGraph) FieldNumber(id, field int64) int64 {
	if row := g.row(id); row != nil {
		return row.numbers[field]
	}
	return 0
}
func (g *inputGraph) FieldText(id, field int64) string {
	if row := g.row(id); row != nil {
		return row.text[field]
	}
	return ""
}
func (g *inputGraph) ReferenceCount(id, field int64) int64 {
	if row := g.row(id); row != nil {
		return int64(len(row.references[field]))
	}
	return 0
}
func (g *inputGraph) ReferenceAt(id, field, position int64) int64 {
	if row := g.row(id); row != nil {
		list := row.references[field]
		if position >= 0 && position < int64(len(list)) {
			return list[position]
		}
	}
	return 0
}
func (g *inputGraph) TextCount(id, field int64) int64 {
	if row := g.row(id); row != nil {
		return int64(len(row.strings[field]))
	}
	return 0
}
func (g *inputGraph) TextAt(id, field, position int64) string {
	if row := g.row(id); row != nil {
		list := row.strings[field]
		if position >= 0 && position < int64(len(list)) {
			return list[position]
		}
	}
	return ""
}

func (g *inputGraph) PredecessorCount(block int64) int64 {
	return g.ReferenceCount(block, fieldBlockPreds)
}
func (g *inputGraph) PredecessorAt(block, position int64) int64 {
	return g.ReferenceAt(block, fieldBlockPreds, position)
}
func (g *inputGraph) PhiOperandCount(phi int64) int64 { return g.ReferenceCount(phi, fieldValueValues) }
func (g *inputGraph) PhiOperandAt(phi, position int64) int64 {
	return g.ReferenceAt(phi, fieldValueValues, position)
}
func (g *inputGraph) PhiBlock(phi int64) int64         { return g.phiBlocks[phi] }
func (g *inputGraph) HasIncoming(phi, pred int64) bool { return g.Incoming(phi, pred) != 0 }
func (g *inputGraph) Incoming(phi, pred int64) int64 {
	block := g.PhiBlock(phi)
	for i := int64(0); i < g.PredecessorCount(block); i++ {
		if g.PredecessorAt(block, i) == pred {
			return g.PhiOperandAt(phi, i)
		}
	}
	return 0
}
