package kv_store_contract_impl

import "github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use"

// MemStore retains the most recent entry. A miss returns zero.
type MemStore struct {
	Key   int64
	Value int64
}

var _ kv_store_contract_use.KVStore = MemStore{}

//golean:verify getAfterPut : ∀ (store : MemStore) (key value : Int64),
//golean:verify+   GetValue (PutValue store key value) key = value
func GetValue(store MemStore, key int64) int64 {
	if key == store.Key {
		return store.Value
	}
	return 0
}

//golean:export
func PutValue(_ MemStore, key, value int64) MemStore {
	return MemStore{Key: key, Value: value}
}

func (store MemStore) Get(key int64) int64 {
	return GetValue(store, key)
}

func (store MemStore) Put(key, value int64) kv_store_contract_use.KVStore {
	return PutValue(store, key, value)
}
