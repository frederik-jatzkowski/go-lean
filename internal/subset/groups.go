package subset

import (
	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"golang.org/x/tools/go/ssa"
)

// Keep the collection representation uniform among functions that call each
// other. Roots from one Go source file also share a representation to preserve
// the exposed signature of existing proof companions.
func representationGroups(program gosource.Program, functions []*ssa.Function) []int {
	parents := make([]int, len(functions))
	index := make(map[*ssa.Function]int, len(functions))
	for i, fn := range functions {
		parents[i] = i
		index[fn] = i
	}
	group := func(i int) int {
		for i != parents[i] {
			parents[i] = parents[parents[i]]
			i = parents[i]
		}
		return i
	}
	union := func(a, b int) { parents[group(a)] = group(b) }
	files := make(map[string]int)
	for _, root := range program.Roots {
		i := index[root]
		file := root.Prog.Fset.PositionFor(root.Pos(), false).Filename
		if other, ok := files[file]; ok {
			union(i, other)
		} else {
			files[file] = i
		}
	}
	for i, fn := range functions {
		for _, block := range fn.Blocks {
			for _, instruction := range block.Instrs {
				call, ok := instruction.(*ssa.Call)
				if !ok {
					continue
				}
				if j, exists := index[call.Call.StaticCallee()]; exists {
					union(i, j)
				}
				for _, arg := range call.Call.Args {
					var callback *ssa.Function
					switch arg := arg.(type) {
					case *ssa.MakeClosure:
						callback, _ = arg.Fn.(*ssa.Function)
					case *ssa.Function:
						callback = arg
					}
					if j, exists := index[callback]; exists {
						union(i, j)
					}
				}
			}
		}
	}
	for i := range parents {
		parents[i] = group(i)
	}
	return parents
}
