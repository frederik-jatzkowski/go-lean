package kv_store_contract_use

// KVStore describes a functional update followed by a read of the updated key.
type KVStore interface {
	Get(key int64) int64
	//golean:law get_after_put : ∀ s k v, Get (Put s k v) k = v
	Put(key, value int64) KVStore
}

func put(store KVStore, key, value int64) KVStore {
	return store.Put(key, value)
}

//golean:verify
func CacheAndFetch(store KVStore, key, value int64) int64 {
	return put(store, key, value).Get(key)
}
