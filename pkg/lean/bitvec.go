package lean

// BitVec models Lean's BitVec w for widths from 0 through 64.
// Index zero is the least significant bit. The zero value has width zero.
type BitVec struct {
	width uint
	value uint64
}

// NewBitVec keeps the low width bits of value and returns None for widths
// greater than 64.
func NewBitVec(width uint, value uint64) Option[BitVec] {
	if width > 64 {
		return None[BitVec]()
	}
	if width < 64 {
		value &= (uint64(1) << width) - 1
	}
	return Some(BitVec{width: width, value: value})
}

// Width returns the fixed width of the vector.
func (b BitVec) Width() uint {
	return b.width
}

// ToUint64 returns the unsigned value of the bits.
func (b BitVec) ToUint64() uint64 {
	return b.value
}

// Get returns the bit at index, or None if index is out of bounds.
func (b BitVec) Get(index uint) Option[bool] {
	if index >= b.width {
		return None[bool]()
	}
	return Some(b.value&(uint64(1)<<index) != 0)
}

// Set replaces the bit at index. An out-of-bounds index leaves b unchanged.
func (b BitVec) Set(index uint, value bool) BitVec {
	if index >= b.width {
		return b
	}
	mask := uint64(1) << index
	if value {
		b.value |= mask
	} else {
		b.value &^= mask
	}
	return b
}
