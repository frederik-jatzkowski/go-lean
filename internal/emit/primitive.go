package emit

import (
	"fmt"
	"strings"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
)

func (r renderer) primitive(value ir.Primitive) string {
	call := func(name string, args ...string) string {
		return "(_root_." + name + " " + strings.Join(args, " ") + ")"
	}
	as := func(typ ir.Type, value string) string {
		return "(" + value + " : " + leanType(typ) + ")"
	}
	nat := func(index ir.Expr) string { return "(" + r.expr(index) + ").toNat" }
	switch v := value.Case().(type) {
	case ir.EmptyValue:
		switch v.Type.Kind() {
		case ir.Array:
			return as(v.Type, "#[]")
		case ir.ByteArray:
			return "_root_.ByteArray.empty"
		case ir.OrderedMap:
			return as(v.Type, "_root_.Std.TreeMap.empty")
		case ir.OrderedSet:
			return as(v.Type, "_root_.Std.TreeSet.empty")
		case ir.Option, ir.Box:
			return as(v.Type, "_root_.Option.none")
		case ir.List:
			return as(v.Type, "[]")
		case ir.BitVec:
			return as(v.Type, "⟨⟨0, by decide⟩, _root_.BitVec.ofNat 0 0⟩")
		}
	case ir.MakeNone:
		return as(v.Type, "_root_.Option.none")
	case ir.ListNil:
		return as(v.Type, "[]")
	case ir.ArrayGet:
		return "(" + r.expr(v.Array) + ")[" + nat(v.Index) + "]?"
	case ir.ByteArrayGet:
		return "(" + r.expr(v.Bytes) + ")[" + nat(v.Index) + "]?"
	case ir.BitVecGet:
		return "((" + r.expr(v.Bits) + ").2.getLsb? " + nat(v.Index) + ")"
	case ir.BitVecSet:
		return as(v.Type, fmt.Sprintf("(let bits := %s; let i := %s; if i < bits.1.val then "+
			"let mask := _root_.BitVec.ofNat bits.1.val (1 <<< i); "+
			"⟨bits.1, if %s then bits.2 ||| mask else bits.2 &&& ~~~mask⟩ else bits)", r.expr(v.Bits), nat(v.Index), r.expr(v.Value)))
	case ir.CollectionSize:
		return "(" + r.word + ".ofNat (" + r.expr(v.Collection) + ").size)"
	case ir.MakeBitVec:
		return fmt.Sprintf("(let w := %s; (if h : w ≤ 64 then _root_.Option.some ⟨⟨w, h⟩, _root_.BitVec.ofNat w %s⟩ else _root_.Option.none : _root_.Option %s))",
			nat(v.Width), nat(v.Value), leanType(ir.NewTypeBitVecType(ir.BitVecType{})))
	case ir.BitVecWidth:
		return "(" + r.word + ".ofNat (" + r.expr(v.Bits) + ").1.val)"
	case ir.BitVecToUint64:
		return "(_root_.UInt64.ofNat (" + r.expr(v.Bits) + ").2.toNat)"
	case ir.MakeSome:
		return call("Option.some", r.expr(v.Value))
	case ir.ListCons:
		return call("List.cons", r.expr(v.Head), r.expr(v.Tail))
	case ir.ListIsEmpty:
		return call("List.isEmpty", r.expr(v.Items))
	case ir.OptionIsSome:
		return call("Option.isSome", r.expr(v.Option))
	case ir.OptionUnwrapOr:
		return call("Option.getD", r.expr(v.Option), r.expr(v.Fallback))
	case ir.BoxRead:
		return call("Option.getD", r.expr(v.Box), r.expr(v.Fallback))
	case ir.ArrayPush:
		return call("Array.push", r.expr(v.Array), r.expr(v.Value))
	case ir.ByteArrayPush:
		return call("ByteArray.push", r.expr(v.Bytes), r.expr(v.Value))
	case ir.ArrayPop:
		return call("Array.pop", r.expr(v.Array))
	case ir.ArraySet:
		return call("Array.set!", r.expr(v.Array), nat(v.Index), r.expr(v.Value))
	case ir.ByteArraySet:
		return call("ByteArray.set!", r.expr(v.Bytes), nat(v.Index), r.expr(v.Value))
	case ir.ByteArrayExtract:
		return call("ByteArray.extract", r.expr(v.Bytes), nat(v.Start), nat(v.End))
	case ir.MapFind:
		return call("Std.TreeMap.get?", r.expr(v.Map), r.expr(v.Key))
	case ir.MapContains:
		return call("Std.TreeMap.contains", r.expr(v.Map), r.expr(v.Key))
	case ir.MapInsert:
		return call("Std.TreeMap.insert", r.expr(v.Map), r.expr(v.Key), r.expr(v.Value))
	case ir.MapErase:
		return call("Std.TreeMap.erase", r.expr(v.Map), r.expr(v.Key))
	case ir.SetContains:
		return call("Std.TreeSet.contains", r.expr(v.Set), r.expr(v.Key))
	case ir.SetInsert:
		return call("Std.TreeSet.insert", r.expr(v.Set), r.expr(v.Key))
	case ir.SetErase:
		return call("Std.TreeSet.erase", r.expr(v.Set), r.expr(v.Key))
	}
	panic(fmt.Sprintf("unexpected IR primitive %T", value.Case()))
}
