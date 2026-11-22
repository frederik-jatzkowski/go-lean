import kv_store_contract_use.kv_store_contract_use_gen

namespace GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use.Proofs

theorem cache_and_fetch_returns_written : Laws.cache_and_fetch_returns_written := by
  intro Handle contract store key value
  exact contract.get_after_put store key value

end GoLean.«github.com/frederik-jatzkowski/go-lean/examples/provable/kv_store_contract_use».kv_store_contract_use.Proofs
