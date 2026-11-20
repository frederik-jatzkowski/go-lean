package transpile

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/gosource"
	"github.com/frederik-jatzkowski/go-lean/internal/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/subset"
	"golang.org/x/tools/go/ssa"
)

type interfaceOperation struct {
	handle ir.Type
	method string
}

func (op interfaceOperation) name() string {
	return strings.TrimPrefix(string(op.handle), "interface:") + "." + op.method
}

// A summary records whether a read or an effect is possible. Sequential
// composition rejects a possible read after an effect.
type pathSummary uint8

const (
	readCalls pathSummary = 1 << iota
	effectCalls
)

func (before pathSummary) followedBy(after pathSummary) (pathSummary, error) {
	if before&effectCalls != 0 && after&readCalls != 0 {
		return 0, fmt.Errorf("readonly interface call after an effect on one control-flow path")
	}
	return before | after, nil
}

var traceType = ir.SliceType(ir.Type("String"))

func appendTrace(before, after ir.Expr) ir.Expr {
	if before == ir.Trace("") {
		return after
	}
	if after == ir.Trace("") {
		return before
	}
	return ir.TraceAppend{Before: before, After: after}
}

type tracedFunction struct {
	summary pathSummary
	symbol  ir.Symbol
}

type traceCompiler struct {
	root     ir.Symbol
	models   map[ir.Symbol]ir.Function
	abstract map[ir.Symbol]map[ir.Symbol]bool
	allowed  map[interfaceOperation]bool
	used     map[interfaceOperation]bool
	compiled map[ir.Symbol]tracedFunction
	variants []ir.Function
	binders  int
}

func traceVerificationRoots(program gosource.Program, model *ir.Program, abstract map[ir.Symbol]map[ir.Symbol]bool) error {
	models := make(map[ir.Symbol]ir.Function)
	for _, fn := range model.Functions {
		models[fn.Symbol] = fn
	}
	for _, fn := range program.Roots {
		entries := program.Directives[fn].InterfaceCalls
		if len(entries) == 0 {
			continue
		}
		if err := checkTraceCallbacks(fn, make(map[*ssa.Function]bool)); err != nil {
			return fmt.Errorf("%s: %w", entries[0].Position, err)
		}
		root := rootSymbol(program, fn)
		compiler := traceCompiler{
			root: root, models: models, abstract: abstract, allowed: make(map[interfaceOperation]bool),
			used: make(map[interfaceOperation]bool), compiled: make(map[ir.Symbol]tracedFunction),
		}
		for _, entry := range entries {
			compiler.allowed[interfaceOperation{subset.InterfaceHandle(entry.Interface), entry.Method.Name()}] = entry.Effect
		}
		if _, err := compiler.function(root); err != nil {
			return fmt.Errorf("%s: strict proof for %s: %w", entries[0].Position, fn.Name(), err)
		}
		for _, entry := range entries {
			op := interfaceOperation{subset.InterfaceHandle(entry.Interface), entry.Method.Name()}
			if !compiler.used[op] {
				return fmt.Errorf("%s: unused interface boundary for %s", entry.Position, op.name())
			}
		}
		if model.TracedRoots == nil {
			model.TracedRoots = make(map[ir.Symbol]bool)
		}
		model.TracedRoots[root] = true
		model.Functions = append(model.Functions, compiler.variants...)
	}
	return nil
}

func checkTraceCallbacks(fn *ssa.Function, seen map[*ssa.Function]bool) error {
	if seen[fn] {
		return nil
	}
	seen[fn] = true
	for _, block := range fn.Blocks {
		for _, instruction := range block.Instrs {
			switch ins := instruction.(type) {
			case *ssa.MakeClosure:
				return fmt.Errorf("callbacks and closures are unsupported in strict proofs (%s)", fn.Name())
			case *ssa.Call:
				if ins.Call.IsInvoke() || subset.IsLength(ins) ||
					subset.IntegerExtremum(ins) != "" || subset.IsStringSliceCapacity(ins) {
					continue
				}
				target := ins.Call.StaticCallee()
				if target == nil || target.Parent() != nil {
					return fmt.Errorf("opaque calls and callbacks are unsupported in strict proofs (%s)", fn.Name())
				}
				if err := checkTraceCallbacks(target, seen); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func (c *traceCompiler) function(symbol ir.Symbol) (tracedFunction, error) {
	if result, ok := c.compiled[symbol]; ok {
		return result, nil
	}
	fn, ok := c.models[symbol]
	if !ok || len(c.abstract[symbol]) != 0 {
		return tracedFunction{}, fmt.Errorf("opaque or abstract callee %s is unsupported", symbol.Name)
	}
	if fn.CanPanic || fn.Loop != nil || fn.Fuel != nil {
		return tracedFunction{}, fmt.Errorf("%s must have an acyclic, total model", symbol.Name)
	}
	body, summary, err := c.body(fn.Body, 0, ir.Trace(""))
	if err != nil {
		return tracedFunction{}, fmt.Errorf("%s: %w", symbol.Name, err)
	}
	result := tracedFunction{summary: summary, symbol: symbol}
	if symbol == c.root || summary&effectCalls != 0 {
		if symbol != c.root {
			result.symbol.Name = c.root.Name + "$trace$" + strconv.Itoa(len(c.variants)) + "$" + symbol.Name
		}
		fn.Symbol, fn.Body, fn.Traced = result.symbol, body, true
		fn.Result = ir.ProductType(fn.Result, traceType)
		c.variants = append(c.variants, fn)
	}
	c.compiled[symbol] = result
	return result, nil
}

func (c *traceCompiler) body(original ir.Body, summary pathSummary, trace ir.Expr) (ir.Body, pathSummary, error) {
	var body ir.Body
	for _, binding := range original.Bindings {
		switch call := binding.Value.(type) {
		case ir.InterfaceCall:
			op := interfaceOperation{call.Contract, call.Method}
			effect, allowed := c.allowed[op]
			if !allowed {
				return ir.Body{}, 0, fmt.Errorf("interface call %s is missing from the //golean:boundary allowlist", op.name())
			}
			c.used[op] = true
			next := readCalls
			if effect {
				next = effectCalls
				trace = appendTrace(trace, ir.Trace(op.name()))
			}
			var err error
			summary, err = summary.followedBy(next)
			if err != nil {
				return ir.Body{}, 0, fmt.Errorf("%s: %w", op.name(), err)
			}
		case ir.Call:
			callee, err := c.function(call.Callee)
			if err != nil {
				return ir.Body{}, 0, err
			}
			summary, err = summary.followedBy(callee.summary)
			if err != nil {
				return ir.Body{}, 0, fmt.Errorf("call to %s: %w", call.Callee.Name, err)
			}
			if callee.summary&effectCalls != 0 {
				call.Callee = callee.symbol
				c.binders++
				pair := ir.Binder{Name: "$trace", Index: c.binders, Type: ir.ProductType(binding.Binder.Type, traceType)}
				body.Bindings = append(body.Bindings, ir.Binding{Binder: pair, Value: call})
				binding.Value = ir.PairField{Value: ir.Ref(pair)}
				trace = appendTrace(trace, ir.PairField{Value: ir.Ref(pair), Second: true})
			}
		}
		body.Bindings = append(body.Bindings, binding)
	}
	switch end := original.Result.(type) {
	case ir.Return:
		body.Result = ir.Return{Value: ir.Pair{Left: end.Value, Right: trace}}
	case ir.If:
		then, thenSummary, err := c.body(end.Then, summary, trace)
		if err != nil {
			return ir.Body{}, 0, err
		}
		otherwise, elseSummary, err := c.body(end.Else, summary, trace)
		if err != nil {
			return ir.Body{}, 0, err
		}
		body.Result = ir.If{Condition: end.Condition, Then: then, Else: otherwise}
		summary = thenSummary | elseSummary
	default:
		return ir.Body{}, 0, fmt.Errorf("strict proofs require an acyclic, total model")
	}
	return body, summary, nil
}
