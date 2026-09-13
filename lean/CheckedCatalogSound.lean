import Ramsey3683Bootstrap.Certificate
import Kernel.CheckedCatalog

set_option autoImplicit false
namespace Compact3684.Log18

theorem CheckedChunk.entry_valid (c : CheckedChunk) (i : Nat) :
    Certificate.LogValid (c.entry i) := by
  change Contains ((c.entry i).lo,(c.entry i).hi)
    (Real.log (((c.entry i).argument : ℝ)/scale))
  apply catalogAll_sound (Codec.packedCatalog c.count c.payload) c.checked.2
  rw [CheckedChunk.entry,Codec.catalogAt_eq_get c.count c.payload (i%c.count) (Nat.mod_lt _ c.positive)]
  exact List.getElem_mem _

theorem CheckedCatalog.all_valid (i : Nat) : Certificate.LogValid (CheckedCatalog.entry i) :=
  (CheckedCatalog.chunks (i/1024)).entry_valid (i%1024)

#print axioms CheckedCatalog.all_valid
end Compact3684.Log18
