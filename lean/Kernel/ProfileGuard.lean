import Kernel.Log18

set_option autoImplicit false
namespace Compact3684.ProfileCheck
open Log18 (q scale)

structure Line where
  a : Int
  b : Int
  deriving DecidableEq, Repr

def deltaA (lines : Nat → Line) (i : Nat) : Int := (lines (i+1)).a-(lines i).a
def deltaB (lines : Nat → Line) (i : Nat) : Int := (lines i).b-(lines (i+1)).b

def shapeGuard (lines : Nat → Line) (n i : Nat) : Bool :=
  decide (0 < (lines i).a ∧ 0 < (lines i).b ∧
    (i < n → (lines i).a < (lines (i+1)).a ∧ (lines (i+1)).b < (lines i).b) ∧
    (i+1 < n → deltaA lines i*deltaB lines (i+1) < deltaA lines (i+1)*deltaB lines i))

def activeGuard (lines : Nat → Line) (n i : Nat) (num den : Int) : Bool :=
  decide (0 < den ∧ i ≤ n ∧
    (0 < i → deltaA lines (i-1)*den ≤ num*deltaB lines (i-1)) ∧
    (i < n → num*deltaB lines i ≤ deltaA lines i*den))

def supportGuard (lines : Nat → Line) (n i j : Nat) (w a b : Int) : Bool :=
  decide (i ≤ n ∧ j ≤ n ∧ 0 ≤ w ∧ w ≤ scale ∧
    w*(lines i).a+(scale-w)*(lines j).a ≤ scale*a ∧
    w*((lines i).a+(lines i).b)+(scale-w)*((lines j).a+(lines j).b) ≤ scale*(a+b))

def lineAt (payload index : Nat) : Line :=
  let raw := payload >>> (128*index)
  ⟨Int.ofNat (raw % 18446744073709551616),
    Int.ofNat ((raw >>> 64) % 18446744073709551616)⟩

structure RegionWitness where
  a : Int
  b : Int
  abi : Nat
  abj : Nat
  abw : Int
  bai : Nat
  baj : Nat
  baw : Int
  deriving DecidableEq, Repr

def regionAt (payload index : Nat) : RegionWitness :=
  let raw := payload >>> (240*index)
  ⟨Int.ofNat (raw % 281474976710656), Int.ofNat ((raw >>> 48) % 281474976710656),
    (raw >>> 96) % 65536, (raw >>> 112) % 65536,
    Int.ofNat ((raw >>> 128) % 1099511627776),
    (raw >>> 168) % 65536, (raw >>> 184) % 65536,
    Int.ofNat ((raw >>> 200) % 1099511627776)⟩

def regionGuard (lines : Nat → Line) (n : Nat) (r : RegionWitness) : Bool :=
  decide (50 < r.a ∧ 50 < r.b) &&
    supportGuard lines n r.abi r.abj r.abw ((r.a-50)*1000000) ((r.b-50)*1000000) &&
    supportGuard lines n r.bai r.baj r.baw ((r.b-50)*1000000) ((r.a-50)*1000000)

end Compact3684.ProfileCheck
