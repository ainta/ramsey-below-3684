import Kernel.Log18

/-! Compact, untrusted proof-data encoding. The production representation
uses only natural-number operations reducible by the kernel. -/
namespace Compact3684.Codec
open Compact3684.Log18

/-- Experimental text decoder, not used by production kernel guards. -/
def catalog (payload : String) : Option (List CatalogEntry) :=
  (payload.splitOn ";").mapM fun line =>
    match line.splitOn "," with
    | [n,lo,hi] => do
      let nn ← n.toInt?
      let ll ← lo.toInt?
      let hh ← hi.toInt?
      pure (CatalogEntry.mk nn ll hh)
    | _ => none

def signed (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n/2) else -(Int.ofNat (n/2))-1

def catalogEntry (payload : Nat) : CatalogEntry :=
  ⟨Int.ofNat (payload % 1099511627776),
   signed ((payload / 1099511627776) % 36893488147419103232),
   signed ((payload / 40564819207303340847894502572032) % 36893488147419103232)⟩

def packedCatalog : Nat → Nat → List CatalogEntry
  | 0, _ => []
  | count+1, payload => catalogEntry payload :: packedCatalog count
      (payload / 1496577676626844588240573268701473812127674924007424)

def catalogAt (payload index : Nat) : CatalogEntry := catalogEntry (payload >>> (170*index))

theorem packedCatalog_length (count payload : Nat) : (packedCatalog count payload).length = count := by
  induction count generalizing payload with
  | zero => rfl
  | succ count ih => simp only [packedCatalog,List.length_cons,ih]

theorem packedCatalog_get (count payload index : Nat) (hi : index < count) :
    (packedCatalog count payload)[index]'(by simpa only [packedCatalog_length] using hi) =
      catalogEntry (payload / 1496577676626844588240573268701473812127674924007424^index) := by
  induction count generalizing payload index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp [packedCatalog]
    | succ index =>
      simpa only [packedCatalog,List.getElem_cons_succ,Nat.pow_succ',Nat.div_div_eq_div_mul] using
        ih (payload/1496577676626844588240573268701473812127674924007424) index (by omega)

theorem catalogAt_eq_get (count payload index : Nat) (hi : index < count) :
    catalogAt payload index =
      (packedCatalog count payload)[index]'(by simpa only [packedCatalog_length] using hi) := by
  rw [packedCatalog_get count payload index hi]
  have hbase : (2 : Nat)^170 = 1496577676626844588240573268701473812127674924007424 := by decide +kernel
  simp only [catalogAt,Nat.shiftRight_eq_div_pow,Nat.pow_mul,hbase]

end Compact3684.Codec
