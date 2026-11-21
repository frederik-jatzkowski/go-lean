package subset

import (
	"go/constant"
	"slices"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"golang.org/x/tools/go/ssa"
)

func stringToBytes(conv *ssa.Convert) bool {
	return Type(conv.X.Type()) == ir.Bytes && Type(conv.Type()).SliceElem() == ir.UInt8
}

// collectionOwnership identifies the allocation whose contents a handle sees.
type collectionOwnership struct {
	roots map[ssa.Value]ssa.Value
}

func analyzeCollections(fn *ssa.Function) (collectionOwnership, error) {
	ownership := collectionOwnership{roots: make(map[ssa.Value]ssa.Value)}
	var sites []ssa.Value
	for _, block := range fn.Blocks {
		for _, ins := range block.Instrs {
			switch ins := ins.(type) {
			case *ssa.Convert:
				if stringToBytes(ins) {
					sites = append(sites, ins)
				}
			case *ssa.MakeSlice:
				if Type(ins.Type()).SliceElem() != "" {
					sites = append(sites, ins)
				}
			case *ssa.MakeMap:
				if key, _ := Type(ins.Type()).MapShape(); key != "" {
					sites = append(sites, ins)
				}
			case *ssa.Slice:
				if _, ok := FixedSliceAllocation(ins); ok {
					sites = append(sites, ins)
				}
			}
		}
	}
	for _, site := range sites {
		handles := collectionHandles(fn, site)
		if err := checkCollectionUses(fn, site, handles); err != nil {
			return collectionOwnership{}, err
		}
		for handle := range handles {
			if ownership.roots[handle] != nil {
				return collectionOwnership{}, diagnostic(fn, handle.Pos(), "collection handle merges distinct allocations")
			}
			ownership.roots[handle] = site
		}
	}
	return ownership, nil
}

// FixedSliceAllocation recognizes make lowered to a fresh zeroed backing array.
// The array must be used only to form the slice, which is the tracked handle.
func FixedSliceAllocation(slice *ssa.Slice) (int64, bool) {
	array, ok := slice.X.(*ssa.Alloc)
	if !ok || slice.Low != nil || slice.Max != nil || Type(slice.Type()).SliceElem() == "" ||
		len(*array.Referrers()) != 1 || (*array.Referrers())[0] != slice {
		return 0, false
	}
	typ := arrayType(array.Type())
	if typ == nil {
		return 0, false
	}
	if slice.High != nil {
		high, ok := slice.High.(*ssa.Const)
		if !ok || high.Value == nil {
			return 0, false
		}
		n, exact := constant.Int64Val(high.Value)
		if !exact || n < 0 || n > typ.Len() {
			return 0, false
		}
	}
	return typ.Len(), true
}

// Discover aliases through SSA edge transfers and supported append calls. A
// cycle can become known from its incoming allocation before its back edge.
func collectionHandles(fn *ssa.Function, site ssa.Value) map[ssa.Value]bool {
	handles := map[ssa.Value]bool{site: true}
	for changed := true; changed; {
		changed = false
		for _, block := range fn.Blocks {
			for _, ins := range block.Instrs {
				var handle ssa.Value
				switch ins := ins.(type) {
				case *ssa.Phi:
					if slices.ContainsFunc(ins.Edges, func(edge ssa.Value) bool { return handles[edge] }) {
						handle = ins
					}
				case *ssa.Call:
					if builtinNamed(ins, "append") && len(ins.Call.Args) > 0 && handles[ins.Call.Args[0]] {
						handle = ins
					}
				}
				if handle != nil && !handles[handle] {
					handles[handle], changed = true, true
				}
			}
		}
	}
	return handles
}

type ownershipPath struct {
	block, pred *ssa.BasicBlock
	current     ssa.Value
	frozen      bool
}

func checkCollectionUses(fn *ssa.Function, site ssa.Value, handles map[ssa.Value]bool) error {
	if alloc, ok := site.(*ssa.MakeMap); ok {
		if alloc.Reserve != nil && !supportedIndex(alloc.Reserve) {
			return diagnostic(fn, alloc.Pos(), "map allocation requires a supported size")
		}
		literalKeys := mapLiteralUpdates(fn, alloc.Pos())
		for _, use := range *alloc.Referrers() {
			if update, ok := use.(*ssa.MapUpdate); ok && literalKeys[update.Pos()] {
				if _, constant := update.Key.(*ssa.Const); !constant {
					return diagnostic(fn, update.Pos(), "map results require a fresh local allocation with local uses before return: multiple literal keys must be constant")
				}
			}
		}
	}
	pending := []ownershipPath{{block: fn.Blocks[0]}}
	seen := make(map[ownershipPath]bool)
	for len(pending) > 0 {
		path := pending[len(pending)-1]
		pending = pending[:len(pending)-1]
		if seen[path] {
			continue
		}
		seen[path] = true
		current, frozen := path.current, path.frozen
		edge := slices.Index(path.block.Preds, path.pred)
		var transferred *ssa.Phi
		for _, ins := range path.block.Instrs {
			if phi, ok := ins.(*ssa.Phi); ok {
				if handles[phi] {
					if edge < 0 || phi.Edges[edge] != path.current || transferred != nil {
						return diagnostic(fn, phi.Pos(), "collection phi requires one live handle from the same allocation on every edge")
					}
					transferred, current = phi, phi
				}
				continue
			}
			if definition, ok := ins.(ssa.Value); ok && definition == site {
				if current != nil {
					return diagnostic(fn, ins.Pos(), "allocate loop-carried mutable collections before the loop")
				}
				current, frozen = site, false
				continue
			}
			for _, operand := range ins.Operands(nil) {
				if operand != nil && handles[*operand] && *operand != current {
					return diagnostic(fn, ins.Pos(), "previous collection view remains live after ownership transfer")
				}
			}
			write, publish := false, false
			switch ins := ins.(type) {
			case *ssa.IndexAddr:
				if !handles[ins.X] {
					break
				}
				for _, use := range *ins.Referrers() {
					store, writes := use.(*ssa.Store)
					load := readsCell(use, ins)
					if use.Block() != ins.Block() || !load && !(writes && store.Addr == ins) ||
						load && !adjacentInstructions(ins, use) {
						return diagnostic(fn, use.Pos(), "collection element address must stay local to its load or store")
					}
				}
			case *ssa.Store:
				if address, ok := ins.Addr.(*ssa.IndexAddr); ok && handles[address.X] {
					if address.X != current {
						return diagnostic(fn, ins.Pos(), "element address outlives its current collection view")
					}
					write = true
				}
				publish = handles[ins.Val]
			case *ssa.MapUpdate:
				write = handles[ins.Map]
			case *ssa.Call:
				if len(ins.Call.Args) > 0 && handles[ins.Call.Args[0]] {
					switch {
					case builtinNamed(ins, "append"):
						write, current = true, ins
					case builtinNamed(ins, "copy"):
						write = true
					}
				}
				if !IsLength(ins) && !IsSliceCapacity(ins) && !builtinNamed(ins, "append") && !builtinNamed(ins, "copy") {
					publish = slices.ContainsFunc(ins.Call.Args, func(arg ssa.Value) bool { return handles[arg] })
				}
			case *ssa.Lookup, *ssa.BinOp, *ssa.Return, *ssa.DebugRef, *ssa.UnOp:
				// Reads and terminal handoffs do not change the local state.
			default:
				for _, operand := range ins.Operands(nil) {
					if operand != nil && handles[*operand] {
						return diagnostic(fn, ins.Pos(), "unsupported view of mutable collection")
					}
				}
			}
			if write && frozen {
				return diagnostic(fn, ins.Pos(), "cannot write collection after publication")
			}
			frozen = frozen || publish
		}
		for _, successor := range path.block.Succs {
			pending = append(pending, ownershipPath{successor, path.block, current, frozen})
		}
	}
	return nil
}

func adjacentInstructions(first, second ssa.Instruction) bool {
	instructions := first.Block().Instrs
	index := slices.Index(instructions, first)
	return index+1 < len(instructions) && instructions[index+1] == second
}
