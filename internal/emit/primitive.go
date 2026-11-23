package emit

import (
	"fmt"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/ir"
)

func (r renderer) primitive(v ir.Primitive) string {
	args := make([]string, len(v.Args))
	for i, arg := range v.Args {
		args[i] = r.expr(arg)
	}
	call := func(name string) string { return "(_root_." + name + " " + strings.Join(args, " ") + ")" }
	as := func(value string) string { return "(" + value + " : " + leanType(v.Type) + ")" }
	nat := func(i int) string { return "(" + args[i] + ").toNat" }
	switch v.Op {
	case ir.Empty:
		switch v.Type.Kind {
		case ir.Array:
			return as("#[]")
		case ir.ByteArray:
			return "_root_.ByteArray.empty"
		case ir.OrderedMap:
			return as("_root_.Std.TreeMap.empty")
		case ir.OrderedSet:
			return as("_root_.Std.TreeSet.empty")
		case ir.Option, ir.Box:
			return as("_root_.Option.none")
		case ir.List:
			return as("[]")
		case ir.BitVec:
			return as("⟨⟨0, by decide⟩, _root_.BitVec.ofNat 0 0⟩")
		}
	case ir.Some:
		return call("Option.some")
	case ir.None:
		return as("_root_.Option.none")
	case ir.Nil:
		return as("[]")
	case ir.Cons:
		return call("List.cons")
	case ir.IsEmpty:
		return call("List.isEmpty")
	case ir.IsSome:
		return call("Option.isSome")
	case ir.UnwrapOr, ir.BoxGet:
		return call("Option.getD")
	case ir.Push:
		if v.Type.Kind == ir.Array {
			return call("Array.push")
		}
		return call("ByteArray.push")
	case ir.Pop:
		return call("Array.pop")
	case ir.Get:
		if v.Type.Kind == ir.BitVec {
			return "((" + args[0] + ").2.getLsb? " + nat(1) + ")"
		}
		return "(" + args[0] + ")[" + nat(1) + "]?"
	case ir.Set:
		if v.Type.Kind == ir.BitVec {
			return as(fmt.Sprintf("(let bits := %s; let i := %s; if i < bits.1.val then "+
				"let mask := _root_.BitVec.ofNat bits.1.val (1 <<< i); "+
				"⟨bits.1, if %s then bits.2 ||| mask else bits.2 &&& ~~~mask⟩ else bits)", args[0], nat(1), args[2]))
		}
		if v.Type.Kind == ir.Array {
			return "(_root_.Array.set! " + args[0] + " " + nat(1) + " " + args[2] + ")"
		}
		return "(_root_.ByteArray.set! " + args[0] + " " + nat(1) + " " + args[2] + ")"
	case ir.Size:
		return "(" + r.word + ".ofNat (" + args[0] + ").size)"
	case ir.Extract:
		return "(_root_.ByteArray.extract " + args[0] + " " + nat(1) + " " + nat(2) + ")"
	case ir.Find:
		return call("Std.TreeMap.get?")
	case ir.Contains, ir.Insert, ir.Erase:
		prefix := "Std.TreeMap."
		if v.Type.Kind == ir.OrderedSet {
			prefix = "Std.TreeSet."
		}
		method := map[ir.PrimitiveOp]string{ir.Contains: "contains", ir.Insert: "insert", ir.Erase: "erase"}[v.Op]
		return call(prefix + method)
	case ir.NewBitVec:
		return fmt.Sprintf("(let w := %s; (if h : w ≤ 64 then _root_.Option.some ⟨⟨w, h⟩, _root_.BitVec.ofNat w %s⟩ else _root_.Option.none : _root_.Option %s))",
			nat(0), nat(1), leanType(ir.Type{Kind: ir.BitVec}))
	case ir.Width:
		return "(" + r.word + ".ofNat (" + args[0] + ").1.val)"
	case ir.ToUint64:
		return "(_root_.UInt64.ofNat (" + args[0] + ").2.toNat)"
	}
	panic(fmt.Sprintf("unexpected primitive %d for type %d", v.Op, v.Type.Kind))
}
