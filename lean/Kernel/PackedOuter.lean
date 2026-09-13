import Kernel.OuterGuard
import Kernel.PackedChain

namespace Compact3684.Outer.Packed
def fractionAt (payload i : Nat) : Fraction :=
  let word := payload >>> (i*512)
  ⟨Int.ofNat (word % (2^256)),Int.ofNat ((word >>> 256) % (2^256))⟩

def coverAt (payload i : Nat) : Cover :=
  let word := Chain.Packed.read64 payload i
  ⟨word % 2,(word >>> 1) % 65536,(word >>> 17) % 8192,
    (word >>> 30) % 65536,(word >>> 46) % 65536⟩
end Compact3684.Outer.Packed
