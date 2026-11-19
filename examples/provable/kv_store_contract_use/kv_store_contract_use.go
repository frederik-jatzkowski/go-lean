package kv_store_contract_use

// KVStore describes a functional update followed by a read of the updated key.
type KVStore interface {
	Get(key int64) int64
	//golean:assume get_after_put : ∀ s k v, Get (Put s k v) k = v
	Put(key, value int64) KVStore
}

func put(store KVStore, key, value int64) KVStore {
	return store.Put(key, value)
}

//golean:verify cache_and_fetch_returns_written : ∀ {Handle : Type} (contract : InterfaceContracts.KVStoreContract Handle) (store : Handle)
//golean:verify+   (key value : Int64),
//golean:verify+   CacheAndFetch contract store key value = value
func CacheAndFetch(store KVStore, key, value int64) int64 {
	return put(store, key, value).Get(key)
}
