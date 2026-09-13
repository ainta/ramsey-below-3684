import Kernel.Codec

set_option autoImplicit false
namespace Compact3684.Log18

structure CheckedChunk where
  count : Nat
  payload : Nat
  positive : 0 < count
  checked : (Codec.packedCatalog count payload).length = count ∧
    (Codec.packedCatalog count payload).all catalogGuard = true

def CheckedChunk.entry (c : CheckedChunk) (i : Nat) : CatalogEntry :=
  Codec.catalogAt c.payload (i%c.count)

end Compact3684.Log18
