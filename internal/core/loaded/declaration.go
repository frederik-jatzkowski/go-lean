package loaded

// CheckDeclaration validates the outer Go declaration before its type and
// body are visited.
//
//golean:export
func (p Program) CheckDeclaration(declaration Declaration, object Object) Diagnostic {
	if object.Kind == FunctionObject {
		signature := p.TypeOrMissing(object.Type)
		if (object.Name == "init" && signature.Receiver == 0) || object.Name == "_" {
			return Diagnostic{Code: UnsupportedFunctionDeclaration, Pos: declaration.Pos, Detail: object.Name}
		}
		return validDiagnostic()
	}
	if object.Kind == TypeName {
		typ := p.TypeOrMissing(object.Type)
		if typ.Kind == AliasType && typ.Generic {
			return Diagnostic{Code: UnsupportedGenericAlias, Pos: declaration.Pos, Detail: object.Name}
		}
		return validDiagnostic()
	}
	if object.Kind == ConstantObject {
		return validDiagnostic()
	}
	if object.Kind == Variable {
		return Diagnostic{Code: UnsupportedPackageVariable, Pos: declaration.Pos, Detail: ""}
	}
	return Diagnostic{Code: UnsupportedDeclaration, Pos: declaration.Pos, Detail: ""}
}

// FitsConstant validates an integer declaration after its type was resolved.
//
//golean:export
func (p Program) FitsConstant(object Object, wordBits int) bool {
	kind := p.Underlying(object.DefaultType).Scalar(wordBits)
	return object.Value.FitsScalar(kind)
}
