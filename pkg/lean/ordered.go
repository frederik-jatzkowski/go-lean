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

// RBMap models Lean's Std.TreeMap with Go's natural key ordering.
// The zero value is empty. Lookup takes logarithmic time, and insertion and
// erasure take linear time in the number of entries.
type RBMap[K OrderedKey, V any] struct {
	entries []mapEntry[K, V]
}

type mapEntry[K OrderedKey, V any] struct {
	key   K
	value V
}

func (m RBMap[K, V]) search(key K) (int, bool) {
	return slices.BinarySearchFunc(m.entries, key, func(entry mapEntry[K, V], key K) int {
		return cmp.Compare(entry.key, key)
	})
}

// Find returns the value at key, or None if the key is absent.
func (m RBMap[K, V]) Find(key K) Option[V] {
	index, found := m.search(key)
	if !found {
		return None[V]()
	}
	return Some(m.entries[index].value)
}

// Contains reports whether key is present.
func (m RBMap[K, V]) Contains(key K) bool {
	_, found := m.search(key)
	return found
}

// Insert associates value with key, replacing any previous value for that key.
func (m RBMap[K, V]) Insert(key K, value V) RBMap[K, V] {
	index, found := m.search(key)
	entry := mapEntry[K, V]{key: key, value: value}
	if found {
		entries := slices.Clone(m.entries)
		entries[index] = entry
		return RBMap[K, V]{entries: entries}
	}
	entries := make([]mapEntry[K, V], len(m.entries)+1)
	copy(entries, m.entries[:index])
	entries[index] = entry
	copy(entries[index+1:], m.entries[index:])
	return RBMap[K, V]{entries: entries}
}

// Erase removes key. An absent key leaves m unchanged.
func (m RBMap[K, V]) Erase(key K) RBMap[K, V] {
	index, found := m.search(key)
	if !found {
		return m
	}
	entries := make([]mapEntry[K, V], len(m.entries)-1)
	copy(entries, m.entries[:index])
	copy(entries[index:], m.entries[index+1:])
	return RBMap[K, V]{entries: entries}
}

// RBSet models Lean's Std.TreeSet with Go's natural key ordering.
// The zero value is empty. Lookup takes logarithmic time, and insertion and
// erasure take linear time in the number of keys.
type RBSet[K OrderedKey] struct {
	keys RBMap[K, struct{}]
}

// Contains reports whether key is in the set.
func (s RBSet[K]) Contains(key K) bool {
	return s.keys.Contains(key)
}

// Insert adds key. A key already in the set leaves s unchanged.
func (s RBSet[K]) Insert(key K) RBSet[K] {
	if s.Contains(key) {
		return s
	}
	return RBSet[K]{keys: s.keys.Insert(key, struct{}{})}
}

// Erase removes key. An absent key leaves s unchanged.
func (s RBSet[K]) Erase(key K) RBSet[K] {
	return RBSet[K]{keys: s.keys.Erase(key)}
}
