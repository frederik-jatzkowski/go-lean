package lean

import (
	"cmp"
	"slices"
)

// OrderedKey constrains ordered map and set keys to strings and integers.
type OrderedKey interface {
	~string | ~int | ~int8 | ~int16 | ~int32 | ~int64 |
		~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

// OrderedMap models Lean's Std.TreeMap with Go's natural key ordering.
// The zero value is empty. Lookup takes logarithmic time, and insertion and
// erasure take linear time in the number of entries.
type OrderedMap[K OrderedKey, V any] struct {
	entries []mapEntry[K, V]
}

type mapEntry[K OrderedKey, V any] struct {
	key   K
	value V
}

func (m OrderedMap[K, V]) search(key K) (int, bool) {
	return slices.BinarySearchFunc(m.entries, key, func(entry mapEntry[K, V], key K) int {
		return cmp.Compare(entry.key, key)
	})
}

// Find returns the value at key, or None if the key is absent.
func (m OrderedMap[K, V]) Find(key K) Option[V] {
	index, found := m.search(key)
	if !found {
		return None[V]()
	}
	return Some(m.entries[index].value)
}

// Contains reports whether key is present.
func (m OrderedMap[K, V]) Contains(key K) bool {
	_, found := m.search(key)
	return found
}

// Insert associates value with key, replacing any previous value for that key.
func (m OrderedMap[K, V]) Insert(key K, value V) OrderedMap[K, V] {
	index, found := m.search(key)
	entry := mapEntry[K, V]{key: key, value: value}
	if found {
		entries := slices.Clone(m.entries)
		entries[index] = entry
		return OrderedMap[K, V]{entries: entries}
	}
	entries := make([]mapEntry[K, V], len(m.entries)+1)
	copy(entries, m.entries[:index])
	entries[index] = entry
	copy(entries[index+1:], m.entries[index:])
	return OrderedMap[K, V]{entries: entries}
}

// Erase removes key. An absent key leaves m unchanged.
func (m OrderedMap[K, V]) Erase(key K) OrderedMap[K, V] {
	index, found := m.search(key)
	if !found {
		return m
	}
	entries := make([]mapEntry[K, V], len(m.entries)-1)
	copy(entries, m.entries[:index])
	copy(entries[index:], m.entries[index+1:])
	return OrderedMap[K, V]{entries: entries}
}

// OrderedSet models Lean's Std.TreeSet with Go's natural key ordering.
// The zero value is empty. Lookup takes logarithmic time, and insertion and
// erasure take linear time in the number of keys.
type OrderedSet[K OrderedKey] struct {
	keys OrderedMap[K, struct{}]
}

// Contains reports whether key is in the set.
func (s OrderedSet[K]) Contains(key K) bool {
	return s.keys.Contains(key)
}

// Insert adds key. A key already in the set leaves s unchanged.
func (s OrderedSet[K]) Insert(key K) OrderedSet[K] {
	if s.Contains(key) {
		return s
	}
	return OrderedSet[K]{keys: s.keys.Insert(key, struct{}{})}
}

// Erase removes key. An absent key leaves s unchanged.
func (s OrderedSet[K]) Erase(key K) OrderedSet[K] {
	return OrderedSet[K]{keys: s.keys.Erase(key)}
}
