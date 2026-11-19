import kv_store_contract_impl.kv_store_contract_impl_gen
import kv_store_contract_use.kv_store_contract_use_proofs

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_impl».kv_store_contract_impl.Proofs

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use
open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use.Proofs

theorem getAfterPut : Laws.getAfterPut := by
  intro store key value
  simp [GetValue, PutValue]

def memStoreContract : InterfaceContracts.KVStoreContract MemStore where
  Get := GetValue
  Put := PutValue
  get_after_put := getAfterPut

theorem cache_and_fetch_mem_store (store : MemStore) (key value : Int64) :
    CacheAndFetch memStoreContract store key value = value :=
  cache_and_fetch_returns_written memStoreContract store key value

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_impl».kv_store_contract_impl.Proofs
