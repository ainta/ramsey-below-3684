import Kernel.ProfileGuard
import Kernel.Elementary

set_option autoImplicit false
namespace Compact3684

theorem checkedRange_at {f : Nat → Bool} {start count i : Nat}
    (h : (List.range count).all (fun j => f (start+j)) = true)
    (hl : start ≤ i) (hh : i < start+count) : f i = true := by
  have hs := List.all_eq_true.mp h (i-start) (List.mem_range.mpr (by omega))
  have he : start+(i-start)=i := by omega
  simpa only [he] using hs

namespace ProfileCheck
structure CheckedRegionChunk (lines : Nat → Line) (n : Nat) where
  count : Nat
  payload : Nat
  positive : 0 < count
  checked : (List.range count).all (fun i => regionGuard lines n (regionAt payload i)) = true

def CheckedRegionChunk.entry {lines : Nat → Line} {n : Nat}
    (c : CheckedRegionChunk lines n) (i : Nat) : RegionWitness := regionAt c.payload (i%c.count)

theorem CheckedRegionChunk.entry_guard {lines : Nat → Line} {n : Nat}
    (c : CheckedRegionChunk lines n) (i : Nat) : regionGuard lines n (c.entry i) = true :=
  List.all_eq_true.mp c.checked (i%c.count) (List.mem_range.mpr (Nat.mod_lt _ c.positive))
end ProfileCheck

namespace Elementary
structure CheckedInitialChunk where
  count : Nat
  payload : Nat
  positive : 0 < count
  checked : (List.range count).all (fun i => initialLineGuard (initialLineAt payload i)) = true

def CheckedInitialChunk.entry (c : CheckedInitialChunk) (i : Nat) : InitialLine :=
  initialLineAt c.payload (i%c.count)

theorem CheckedInitialChunk.entry_guard (c : CheckedInitialChunk) (i : Nat) :
    initialLineGuard (c.entry i) = true :=
  List.all_eq_true.mp c.checked (i%c.count) (List.mem_range.mpr (Nat.mod_lt _ c.positive))
end Elementary
end Compact3684
