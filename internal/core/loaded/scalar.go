package loaded

type ScalarKind uint8

// AllowsIdentityConversion reports whether two underlying basic types are
// the same supported scalar, independent of the target word width.
//
//golean:export
func (t Type) AllowsIdentityConversion(source Type) bool {
	return t.Kind == BasicType && source.Kind == BasicType &&
		t.Basic == source.Basic && t.Scalar(64) != NotScalar
}

const (
	NotScalar ScalarKind = iota
	ScalarBool
	ScalarString
	ScalarInt8
	ScalarInt16
	ScalarInt32
	ScalarInt64
	ScalarUInt8
	ScalarUInt16
	ScalarUInt32
	ScalarUInt64
)

// Scalar classifies basic types at the modeled Go target's word width.
//
//golean:export
func (t Type) Scalar(wordBits int) ScalarKind {
	if t.Basic == "bool" || t.Basic == "untyped bool" {
		return ScalarBool
	}
	if t.Basic == "string" || t.Basic == "untyped string" {
		return ScalarString
	}
	if t.Basic == "int8" {
		return ScalarInt8
	}
	if t.Basic == "int16" {
		return ScalarInt16
	}
	if t.Basic == "int32" || t.Basic == "untyped rune" {
		return ScalarInt32
	}
	if t.Basic == "int64" {
		return ScalarInt64
	}
	if t.Basic == "uint8" {
		return ScalarUInt8
	}
	if t.Basic == "uint16" {
		return ScalarUInt16
	}
	if t.Basic == "uint32" {
		return ScalarUInt32
	}
	if t.Basic == "uint64" {
		return ScalarUInt64
	}
	if t.Basic == "int" || t.Basic == "untyped int" {
		if wordBits == 32 {
			return ScalarInt32
		}
		return ScalarInt64
	}
	if t.Basic == "uint" {
		if wordBits == 32 {
			return ScalarUInt32
		}
		return ScalarUInt64
	}
	return NotScalar
}

func (s ScalarKind) integerWidth() int {
	if s == ScalarInt8 || s == ScalarUInt8 {
		return 8
	}
	if s == ScalarInt16 || s == ScalarUInt16 {
		return 16
	}
	if s == ScalarInt32 || s == ScalarUInt32 {
		return 32
	}
	if s == ScalarInt64 || s == ScalarUInt64 {
		return 64
	}
	return 0
}

// FitsScalar checks the range of an integer constant at the classified width.
//
//golean:export
func (c Constant) FitsScalar(kind ScalarKind) bool {
	if !c.Integer {
		return true
	}
	width := kind.integerWidth()
	if width == 0 {
		return false
	}
	if kind >= ScalarUInt8 {
		return !c.Negative && c.MagnitudeBits <= width
	}
	return c.SignedBits <= width
}
