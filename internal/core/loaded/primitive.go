package loaded

type PrimitiveOp uint8

const (
	OpMakeSome PrimitiveOp = iota + 1
	OpMakeNone
	OpListNil
	OpListCons
	OpListIsEmpty
	OpOptionIsSome
	OpOptionUnwrapOr
	OpBoxRead
	OpArrayPush
	OpByteArrayPush
	OpArrayPop
	OpArrayGet
	OpByteArrayGet
	OpBitVecGet
	OpArraySet
	OpByteArraySet
	OpBitVecSet
	OpCollectionSize
	OpByteArrayExtract
	OpMapFind
	OpMapContains
	OpMapInsert
	OpMapErase
	OpSetContains
	OpSetInsert
	OpSetErase
	OpMakeBitVec
	OpBitVecWidth
	OpBitVecToUint64
)

// CuratedConstructor identifies an allowed package-level constructor.
//
//golean:export
func CuratedConstructor(name string) PrimitiveOp {
	if name == "NewBox" {
		return OpMakeSome
	}
	if name == "Some" {
		return OpMakeSome
	}
	if name == "None" {
		return OpMakeNone
	}
	if name == "Nil" {
		return OpListNil
	}
	if name == "Cons" {
		return OpListCons
	}
	if name == "NewBitVec" {
		return OpMakeBitVec
	}
	return 0
}

// CuratedMethod identifies an allowed method on a curated receiver type.
//
//golean:export
func CuratedMethod(receiver string, name string) PrimitiveOp {
	if receiver == "Array" {
		if name == "Push" {
			return OpArrayPush
		}
		if name == "Pop" {
			return OpArrayPop
		}
		if name == "Get" {
			return OpArrayGet
		}
		if name == "Set" {
			return OpArraySet
		}
		if name == "Size" {
			return OpCollectionSize
		}
	}
	if receiver == "ByteArray" {
		if name == "Push" {
			return OpByteArrayPush
		}
		if name == "Get" {
			return OpByteArrayGet
		}
		if name == "Set" {
			return OpByteArraySet
		}
		if name == "Size" {
			return OpCollectionSize
		}
		if name == "Extract" {
			return OpByteArrayExtract
		}
	}
	if receiver == "OrderedMap" {
		if name == "Find" {
			return OpMapFind
		}
		if name == "Contains" {
			return OpMapContains
		}
		if name == "Insert" {
			return OpMapInsert
		}
		if name == "Erase" {
			return OpMapErase
		}
	}
	if receiver == "OrderedSet" {
		if name == "Contains" {
			return OpSetContains
		}
		if name == "Insert" {
			return OpSetInsert
		}
		if name == "Erase" {
			return OpSetErase
		}
	}
	if receiver == "Box" {
		if name == "IsSome" {
			return OpOptionIsSome
		}
		if name == "Get" {
			return OpBoxRead
		}
	}
	if receiver == "Option" {
		if name == "IsSome" {
			return OpOptionIsSome
		}
		if name == "UnwrapOr" {
			return OpOptionUnwrapOr
		}
	}
	if receiver == "List" {
		if name == "IsEmpty" {
			return OpListIsEmpty
		}
	}
	if receiver == "BitVec" {
		if name == "Get" {
			return OpBitVecGet
		}
		if name == "Set" {
			return OpBitVecSet
		}
		if name == "Width" {
			return OpBitVecWidth
		}
		if name == "ToUint64" {
			return OpBitVecToUint64
		}
	}
	return 0
}
