import PackedNatCatalogBench

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.PackedLookupBench
open Compact3684.PackedCatalogBench (payload)

def lookupGuard (i : Nat) : Bool :=
  let e := Codec.catalogAt payload (i % 1024)
  decide (0 < e.argument ∧ e.lo ≤ e.hi ∧ e.hi < 0)

theorem checked : (List.range 16384).all lookupGuard = true := by decide +kernel

#print axioms checked
end Compact3684.PackedLookupBench
