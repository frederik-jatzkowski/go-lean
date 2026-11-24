package lower

import "github.com/frederik-jatzkowski/go-lean/internal/core/ir"

type primitiveKind uint8

const (
	opMakeSome primitiveKind = iota + 1
	opMakeNone
	opListNil
	opListCons
	opListIsEmpty
	opOptionIsSome
	opOptionUnwrapOr
	opBoxRead
	opArrayPush
	opByteArrayPush
	opArrayPop
	opArrayGet
	opByteArrayGet
	opBitVecGet
	opArraySet
	opByteArraySet
	opBitVecSet
	opCollectionSize
	opByteArrayExtract
	opMapFind
	opMapContains
	opMapInsert
	opMapErase
	opSetContains
	opSetInsert
	opSetErase
	opMakeBitVec
	opBitVecWidth
	opBitVecToUint64
)

var constructors = map[string]primitiveKind{
	"NewBox": opMakeSome, "Some": opMakeSome, "None": opMakeNone, "Nil": opListNil, "Cons": opListCons, "NewBitVec": opMakeBitVec,
}

var methods = map[ir.Kind]map[string]primitiveKind{
	ir.Array:      {"Push": opArrayPush, "Pop": opArrayPop, "Get": opArrayGet, "Set": opArraySet, "Size": opCollectionSize},
	ir.ByteArray:  {"Push": opByteArrayPush, "Get": opByteArrayGet, "Set": opByteArraySet, "Size": opCollectionSize, "Extract": opByteArrayExtract},
	ir.OrderedMap: {"Find": opMapFind, "Contains": opMapContains, "Insert": opMapInsert, "Erase": opMapErase},
	ir.OrderedSet: {"Contains": opSetContains, "Insert": opSetInsert, "Erase": opSetErase},
	ir.Box:        {"IsSome": opOptionIsSome, "Get": opBoxRead},
	ir.Option:     {"IsSome": opOptionIsSome, "UnwrapOr": opOptionUnwrapOr},
	ir.List:       {"IsEmpty": opListIsEmpty},
	ir.BitVec:     {"Get": opBitVecGet, "Set": opBitVecSet, "Width": opBitVecWidth, "ToUint64": opBitVecToUint64},
}

func primitiveExpr(value ir.Primitive) ir.Expr {
	return ir.NewExprPrimitiveExpr(ir.PrimitiveExpr{Primitive: value})
}

func emptyValue(t ir.Type) ir.Expr {
	return primitiveExpr(ir.NewPrimitiveEmptyValue(ir.EmptyValue{Type: t}))
}

func (f *function) primitive(op primitiveKind, t ir.Type, args []ir.Expr) ir.Expr {
	switch op {
	case opMakeSome:
		return primitiveExpr(ir.NewPrimitiveMakeSome(ir.MakeSome{Value: args[0]}))
	case opMakeNone:
		return primitiveExpr(ir.NewPrimitiveMakeNone(ir.MakeNone{Type: t}))
	case opListNil:
		return primitiveExpr(ir.NewPrimitiveListNil(ir.ListNil{Type: t}))
	case opListCons:
		return primitiveExpr(ir.NewPrimitiveListCons(ir.ListCons{Head: args[0], Tail: args[1]}))
	case opListIsEmpty:
		return primitiveExpr(ir.NewPrimitiveListIsEmpty(ir.ListIsEmpty{Items: args[0]}))
	case opOptionIsSome:
		return primitiveExpr(ir.NewPrimitiveOptionIsSome(ir.OptionIsSome{Option: args[0]}))
	case opOptionUnwrapOr:
		return primitiveExpr(ir.NewPrimitiveOptionUnwrapOr(ir.OptionUnwrapOr{Option: args[0], Fallback: args[1]}))
	case opBoxRead:
		return primitiveExpr(ir.NewPrimitiveBoxRead(ir.BoxRead{Box: args[0], Fallback: f.zero(t.Case().(ir.BoxType).Element)}))
	case opArrayPush:
		return primitiveExpr(ir.NewPrimitiveArrayPush(ir.ArrayPush{Array: args[0], Value: args[1]}))
	case opByteArrayPush:
		return primitiveExpr(ir.NewPrimitiveByteArrayPush(ir.ByteArrayPush{Bytes: args[0], Value: args[1]}))
	case opArrayPop:
		return primitiveExpr(ir.NewPrimitiveArrayPop(ir.ArrayPop{Array: args[0]}))
	case opArrayGet:
		return primitiveExpr(ir.NewPrimitiveArrayGet(ir.ArrayGet{Array: args[0], Index: args[1]}))
	case opByteArrayGet:
		return primitiveExpr(ir.NewPrimitiveByteArrayGet(ir.ByteArrayGet{Bytes: args[0], Index: args[1]}))
	case opBitVecGet:
		return primitiveExpr(ir.NewPrimitiveBitVecGet(ir.BitVecGet{Bits: args[0], Index: args[1]}))
	case opArraySet:
		return primitiveExpr(ir.NewPrimitiveArraySet(ir.ArraySet{Array: args[0], Index: args[1], Value: args[2]}))
	case opByteArraySet:
		return primitiveExpr(ir.NewPrimitiveByteArraySet(ir.ByteArraySet{Bytes: args[0], Index: args[1], Value: args[2]}))
	case opBitVecSet:
		return primitiveExpr(ir.NewPrimitiveBitVecSet(ir.BitVecSet{Type: t, Bits: args[0], Index: args[1], Value: args[2]}))
	case opCollectionSize:
		return primitiveExpr(ir.NewPrimitiveCollectionSize(ir.CollectionSize{Collection: args[0]}))
	case opByteArrayExtract:
		return primitiveExpr(ir.NewPrimitiveByteArrayExtract(ir.ByteArrayExtract{Bytes: args[0], Start: args[1], End: args[2]}))
	case opMapFind:
		return primitiveExpr(ir.NewPrimitiveMapFind(ir.MapFind{Map: args[0], Key: args[1]}))
	case opMapContains:
		return primitiveExpr(ir.NewPrimitiveMapContains(ir.MapContains{Map: args[0], Key: args[1]}))
	case opMapInsert:
		return primitiveExpr(ir.NewPrimitiveMapInsert(ir.MapInsert{Map: args[0], Key: args[1], Value: args[2]}))
	case opMapErase:
		return primitiveExpr(ir.NewPrimitiveMapErase(ir.MapErase{Map: args[0], Key: args[1]}))
	case opSetContains:
		return primitiveExpr(ir.NewPrimitiveSetContains(ir.SetContains{Set: args[0], Key: args[1]}))
	case opSetInsert:
		return primitiveExpr(ir.NewPrimitiveSetInsert(ir.SetInsert{Set: args[0], Key: args[1]}))
	case opSetErase:
		return primitiveExpr(ir.NewPrimitiveSetErase(ir.SetErase{Set: args[0], Key: args[1]}))
	case opMakeBitVec:
		return primitiveExpr(ir.NewPrimitiveMakeBitVec(ir.MakeBitVec{Width: args[0], Value: args[1]}))
	case opBitVecWidth:
		return primitiveExpr(ir.NewPrimitiveBitVecWidth(ir.BitVecWidth{Bits: args[0]}))
	case opBitVecToUint64:
		return primitiveExpr(ir.NewPrimitiveBitVecToUint64(ir.BitVecToUint64{Bits: args[0]}))
	default:
		panic("unknown curated operation")
	}
}
