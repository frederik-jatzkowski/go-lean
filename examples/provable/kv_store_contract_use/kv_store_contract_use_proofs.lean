import kv_store_contract_use.kv_store_contract_use_gen

namespace KVStoreContractUse

open GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use

theorem cache_and_fetch_returns_written {Handle : Type}
    (contract : InterfaceContracts.KVStoreContract Handle) (store : Handle) (key value : Int64) :
    CacheAndFetch contract store key value = value :=
  contract.get_after_put store key value

end KVStoreContractUse
