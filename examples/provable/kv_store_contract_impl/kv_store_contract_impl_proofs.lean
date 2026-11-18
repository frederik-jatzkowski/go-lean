import kv_store_contract_impl.kv_store_contract_impl_gen
import kv_store_contract_use.kv_store_contract_use_proofs

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_impl».kv_store_contract_impl
open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use

def memStoreContract : InterfaceContracts.KVStoreContract MemStore where
  Get := GetValue
  Put := PutValue
  get_after_put := by
    intro store key value
    simp [GetValue, PutValue]

theorem cache_and_fetch_mem_store (store : MemStore) (key value : Int64) :
    CacheAndFetch memStoreContract store key value = value :=
  KVStoreContractUse.cache_and_fetch_returns_written memStoreContract store key value
