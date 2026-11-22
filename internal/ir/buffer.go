package ir

import "strings"

func BufferType(elem Type) Type { return Type("buffer:" + elem) }

func (t Type) BufferElem() Type {
	elem, ok := strings.CutPrefix(string(t), "buffer:")
	if !ok {
		return ""
	}
	return Type(elem)
}

type EmptyBuffer struct{}

type BufferLength struct{ Buffer Expr }

type BufferAppend struct{ Buffer, Element Expr }

type BufferSet struct {
	Buffer, Index, Value Expr
	IndexType            Type
}

func (EmptyBuffer) expr()  {}
func (BufferLength) expr() {}
func (BufferAppend) expr() {}
func (BufferSet) expr()    {}
