package lower

import (
	"go/token"
	"go/types"

	"github.com/frederik-jatzkowski/go-lean/internal/core/ir"
	"github.com/frederik-jatzkowski/go-lean/internal/load"
	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
	"golang.org/x/tools/go/packages"
)

func basic(p *packages.Package, pos token.Pos, b *types.Basic) (ir.Type, error) {
	var kind ir.Kind
	switch b.Kind() {
	case types.Bool, types.UntypedBool:
		kind = ir.Bool
	case types.String, types.UntypedString:
		kind = ir.String
	case types.Int8:
		kind = ir.Int8
	case types.Int16:
		kind = ir.Int16
	case types.Int32, types.UntypedRune:
		kind = ir.Int32
	case types.Int64:
		kind = ir.Int64
	case types.Uint8:
		kind = ir.UInt8
	case types.Uint16:
		kind = ir.UInt16
	case types.Uint32:
		kind = ir.UInt32
	case types.Uint64:
		kind = ir.UInt64
	case types.Int, types.UntypedInt:
		kind = ir.Int64
		if p.TypesSizes.Sizeof(types.Typ[types.Int]) == 4 {
			kind = ir.Int32
		}
	case types.Uint:
		kind = ir.UInt64
		if p.TypesSizes.Sizeof(b) == 4 {
			kind = ir.UInt32
		}
	default:
		return ir.Type{}, load.Error(p, pos, "unsupported scalar type %s", b)
	}
	return ir.NewTypeScalarType(ir.ScalarType{Scalar: kind}), nil
}

var curatedTypes = map[string]ir.Kind{
	"Array": ir.Array, "ByteArray": ir.ByteArray, "OrderedMap": ir.OrderedMap, "OrderedSet": ir.OrderedSet,
	"Box": ir.Box, "Option": ir.Option, "BitVec": ir.BitVec, "List": ir.List, "FoldControl": ir.FoldControl,
}

func (c *compiler) goType(p *packages.Package, pos token.Pos, typ types.Type) (ir.Type, error) {
	if named, ok := typ.(interface{ Obj() *types.TypeName }); ok {
		if issue := c.source.TypeIssues[named.Obj()]; issue != nil {
			return ir.Type{}, issue
		}
	}
	switch t := types.Unalias(typ).(type) {
	case *types.Basic:
		return basic(p, pos, t)
	case *types.Named:
		obj := t.Obj()
		if issue := c.source.TypeIssues[obj]; issue != nil {
			return ir.Type{}, issue
		}
		if obj.Pkg() != nil && obj.Pkg().Path() == load.Curated {
			kind, ok := curatedTypes[obj.Name()]
			if !ok {
				break
			}
			var args [2]ir.Type
			for i := range t.TypeArgs().Len() {
				var err error
				args[i], err = c.goType(p, pos, t.TypeArgs().At(i))
				if err != nil {
					return ir.Type{}, err
				}
			}
			return curatedType(kind, args), nil
		}
		if t.TypeParams().Len() != 0 {
			break
		}
		if enum, ok := c.source.Enums[obj]; ok {
			return c.enumType(p, pos, obj, enum)
		}
		switch u := t.Underlying().(type) {
		case *types.Basic:
			return basic(p, pos, u)
		case *types.Struct:
			if obj.Parent() != obj.Pkg().Scope() {
				break
			}
			id := symbol(obj)
			if err := c.depend(p, id.Package, pos); err != nil {
				return ir.Type{}, err
			}
			if c.state[obj] == 0 {
				c.state[obj] = 1
				owner := c.source.Packages[id.Package]
				record := ir.Struct{Symbol: id}
				var fields []ir.Field
				for i := 0; i < u.NumFields(); i++ {
					field := u.Field(i)
					if field.Embedded() || field.Name() == "_" {
						return ir.Type{}, load.Error(owner, field.Pos(), "embedded and blank fields are unsupported")
					}
					if isSelfBox(field.Type(), obj) {
						elem := ir.NewTypeRecordType(ir.RecordType{Symbol: id})
						fields = append(fields, ir.Field{Name: field.Name(), Type: ir.NewTypeBoxType(ir.BoxType{Element: elem})})
						record.Recursive = true
						continue
					}
					ft, err := c.goType(owner, field.Pos(), field.Type())
					if err != nil {
						return ir.Type{}, err
					}
					fields = append(fields, ir.Field{Name: field.Name(), Type: ft})
				}
				out := c.output(id.Package)
				record.Fields = list(fields)
				out.decls = append(out.decls, ir.NewDeclarationStruct(record))
				c.state[obj] = 2
			}
			return ir.NewTypeRecordType(ir.RecordType{Symbol: id}), nil
		}
	}
	return ir.Type{}, load.Error(p, pos, "unsupported type %s", typ)
}

func isSelfBox(typ types.Type, owner *types.TypeName) bool {
	box, ok := types.Unalias(typ).(*types.Named)
	if !ok || box.Obj().Pkg() == nil || box.Obj().Pkg().Path() != load.Curated || box.Obj().Name() != "Box" {
		return false
	}
	payload, ok := types.Unalias(box.TypeArgs().At(0)).(*types.Named)
	return ok && payload.Obj() == owner
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
		return emptyValue(t)
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
