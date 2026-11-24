package lower

import (
	"fmt"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/core/loaded"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func basic(p loaded.Package, pos string, b loaded.Type) (ir.Type, error) {
	kind := b.Scalar(p.WordBits)
	if kind == loaded.NotScalar {
		return ir.Type{}, diagnostic(pos, "unsupported scalar type %s", b.Display)
	}
	return ir.ScalarFromLoaded(kind), nil
}

var curatedTypes = map[string]ir.Kind{
	"Array": ir.Array, "ByteArray": ir.ByteArray, "OrderedMap": ir.OrderedMap, "OrderedSet": ir.OrderedSet,
	"Box": ir.Box, "Option": ir.Option, "BitVec": ir.BitVec, "List": ir.List, "FoldControl": ir.FoldControl,
}

func (c *compiler) unalias(id loaded.TypeID) loaded.Type {
	typ := c.inputType(id)
	if typ.Kind == loaded.AliasType {
		return c.inputType(typ.Underlying)
	}
	return typ
}

func (c *compiler) underlying(id loaded.TypeID) loaded.Type {
	typ := c.unalias(id)
	if typ.Kind == loaded.NamedType {
		return c.inputType(typ.Underlying)
	}
	return typ
}

func (c *compiler) goType(p loaded.Package, pos string, typeID loaded.TypeID) (ir.Type, error) {
	original := c.inputType(typeID)
	if issue := c.object(original.Object).Issue; issue != "" {
		return ir.Type{}, fmt.Errorf("%s", issue)
	}
	t := c.unalias(typeID)
	switch t.Kind {
	case loaded.BasicType:
		return basic(p, pos, t)
	case loaded.NamedType:
		obj := c.object(t.Object)
		if obj.Issue != "" {
			return ir.Type{}, fmt.Errorf("%s", obj.Issue)
		}
		if obj.Package == loaded.Curated {
			if kind, ok := curatedTypes[obj.Name]; ok {
				var args [2]ir.Type
				for i, id := range values(t.Args) {
					var err error
					args[i], err = c.goType(p, pos, id)
					if err != nil {
						return ir.Type{}, err
					}
				}
				return curatedType(kind, args), nil
			}
			break
		}
		if t.Generic {
			break
		}
		if obj.Enum.IsSome() {
			return c.enumType(p, pos, t.Object, obj.Enum.UnwrapOr(loaded.Enum{}))
		}
		u := c.inputType(t.Underlying)
		switch u.Kind {
		case loaded.BasicType:
			return basic(p, pos, u)
		case loaded.StructType:
			if !t.PackageScope {
				break
			}
			id := c.symbol(t.Object)
			if err := c.depend(p, id.Package, pos); err != nil {
				return ir.Type{}, err
			}
			if c.state[t.Object] == 0 {
				c.state[t.Object] = 1
				owner := c.inputPackage(id.Package)
				record := ir.Struct{Symbol: id}
				var fields []ir.Field
				for _, fieldID := range values(u.Fields) {
					field := c.object(fieldID)
					if field.Embedded || field.Name == "_" {
						return ir.Type{}, diagnostic(field.Pos, "embedded and blank fields are unsupported")
					}
					if c.isSelfBox(field.Type, t.Object) {
						elem := ir.NewTypeRecordType(ir.RecordType{Symbol: id})
						fields = append(fields, ir.Field{Name: field.Name, Type: ir.NewTypeBoxType(ir.BoxType{Element: elem})})
						record.Recursive = true
						continue
					}
					ft, err := c.goType(owner, field.Pos, field.Type)
					if err != nil {
						return ir.Type{}, err
					}
					fields = append(fields, ir.Field{Name: field.Name, Type: ft})
				}
				out := c.output(id.Package)
				record.Fields = list(fields)
				out.decls = append(out.decls, ir.NewDeclarationStruct(record))
				c.state[t.Object] = 2
			}
			return ir.NewTypeRecordType(ir.RecordType{Symbol: id}), nil
		}
	}
	return ir.Type{}, diagnostic(pos, "unsupported type %s", original.Display)
}

func (c *compiler) isSelfBox(id loaded.TypeID, owner loaded.ObjectID) bool {
	box := c.unalias(id)
	obj := c.object(box.Object)
	if box.Kind != loaded.NamedType || obj.Package != loaded.Curated || obj.Name != "Box" {
		return false
	}
	payload := c.unalias(at(box.Args, uint(0)))
	return payload.Kind == loaded.NamedType && payload.Object == owner
}

func (c *compiler) zero(t ir.Type) ir.Expr {
	switch t.Kind() {
	case ir.EnumType:
		id := t.Case().(ir.EnumTypeRef).Symbol
		for _, decl := range c.output(id.Package).decls {
			if enum, ok := decl.Case().(ir.Enum); ok && enum.Symbol == id {
				variant := lean.FoldListUntil(enum.Variants, variantLookup{Remaining: enum.Default}, findVariant).State.Field
				return ir.NewExprConstructor(ir.Constructor{Enum: id, Variant: variant.Name, Value: c.zero(variant.Type)})
			}
		}
		panic("missing enum for Go zero value")
	case ir.Record:
		id := t.Case().(ir.RecordType).Symbol
		for _, decl := range c.output(id.Package).decls {
			if record, ok := decl.Case().(ir.Struct); ok && record.Symbol == id {
				fields := lean.FoldList(record.Fields, zeroFields{Compiler: c}, appendZeroField).Fields
				return ir.NewExprStructLiteral(ir.StructLiteral{Type: id, Fields: exprSeq(fields)})
			}
		}
		panic("missing record for Go zero value")
	case ir.Bool:
		return ir.NewExprConstant(ir.Constant{Type: t, Value: "false"})
	case ir.String:
		return ir.NewExprConstant(ir.Constant{Type: t})
	case ir.FoldControl:
		return ir.NewExprFoldControlLiteral(ir.FoldControlLiteral{State: c.zero(t.Case().(ir.FoldControlType).Element), Stop: c.zero(ir.NewTypeScalarType(ir.ScalarType{Scalar: ir.Bool}))})
	default:
		if t.Kind() < ir.Record {
			return ir.NewExprConstant(ir.Constant{Type: t, Value: "0"})
		}
		return ir.NewEmptyValueExpr(t)
	}
}

func curatedType(kind ir.Kind, args [2]ir.Type) ir.Type {
	switch kind {
	case ir.Array:
		return ir.NewTypeArrayType(ir.ArrayType{Element: args[0]})
	case ir.ByteArray:
		return ir.NewTypeByteArrayType(ir.ByteArrayType{})
	case ir.OrderedMap:
		return ir.NewTypeMapType(ir.MapType{Key: args[0], Value: args[1]})
	case ir.OrderedSet:
		return ir.NewTypeSetType(ir.SetType{Key: args[0]})
	case ir.Option:
		return ir.NewTypeOptionType(ir.OptionType{Element: args[0]})
	case ir.BitVec:
		return ir.NewTypeBitVecType(ir.BitVecType{})
	case ir.List:
		return ir.NewTypeListType(ir.ListType{Element: args[0]})
	case ir.FoldControl:
		return ir.NewTypeFoldControlType(ir.FoldControlType{Element: args[0]})
	case ir.Box:
		return ir.NewTypeBoxType(ir.BoxType{Element: args[0]})
	default:
		panic("unknown curated type")
	}
}

type variantLookup struct {
	Remaining int
	Field     ir.Field
}

func findVariant(field ir.Field, state variantLookup) lean.FoldControl[variantLookup] {
	if state.Remaining == 0 {
		state.Field = field
		return lean.FoldControl[variantLookup]{State: state, Stop: true}
	}
	state.Remaining--
	return lean.FoldControl[variantLookup]{State: state}
}

type zeroFields struct {
	Compiler *compiler
	Fields   []ir.Expr
}

func appendZeroField(field ir.Field, state zeroFields) zeroFields {
	state.Fields = append(state.Fields, state.Compiler.zero(field.Type))
	return state
}
