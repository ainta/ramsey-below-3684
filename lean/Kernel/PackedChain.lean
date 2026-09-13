import Kernel.ChainGuard

set_option autoImplicit false
namespace Compact3684.Chain.Packed

def read64 (p i : Nat) : Nat := (p >>> (64*i)) % 18446744073709551616
def read128 (p i : Nat) : Nat := (p >>> (128*i)) % 340282366920938463463374607431768211456
def read256 (p i : Nat) : Nat := (p >>> (256*i)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936

structure NodeBlob where
  bits : Nat
  value : Nat
  finish : Nat
  begin : Nat
  pref : Nat
  blue : Nat
  controls : Nat

def nodeAt (blob : NodeBlob) (i : Nat) (regions : Nat → ProfileCheck.RegionWitness) : Node :=
  let m := read128 blob.bits i
  let blue := read128 blob.blue i
  let controls := read256 blob.controls i
  let regionId := (m >>> 56) % 16384
  { row := m % 8192
    col := (m >>> 13) % 512
    start := (m >>> 22) % 8192
    kind := (m >>> 35) % 2
    baseKind := (m >>> 36) % 2
    base := (m >>> 37) % 524288
    region := regionId
    block := (m >>> 70) % 2048
    pathStart := (m >>> 81) % 16777216
    pathCount := (m >>> 105) % 8192
    value := Int.ofNat (read128 blob.value i)
    finish := Int.ofNat (read128 blob.finish i)
    begin := Int.ofNat (read128 blob.begin i)
    pref := Int.ofNat (read128 blob.pref i)
    cost := Int.ofNat (blue % 281474976710656)
    density := Int.ofNat ((blue >>> 48) % 1099511627776)
    logBlue := (blue >>> 88) % 524288
    seed := ⟨(regions regionId).a,(regions regionId).b,
      Int.ofNat (controls % 18446744073709551616),
      Int.ofNat ((controls >>> 64) % 1099511627776),
      Int.ofNat ((controls >>> 104) % 1099511627776)⟩
    logMu := (controls >>> 144) % 524288
    logOneMinusMu := (controls >>> 163) % 524288
    logPi := (controls >>> 182) % 524288 }

structure RunBlob where
  bits : Nat
  finish : Nat

def runAt (blob : RunBlob) (i : Nat) : Run :=
  let m := read64 blob.bits i
  ⟨m % 524288,(m >>> 19) % 524288,(m >>> 38) % 524288,
    Int.ofNat (read128 blob.finish i)⟩

def blockAt (blob i : Nat) : Block :=
  let m := read64 blob i
  ⟨m % 8192,(m >>> 13) % 8192,(m >>> 26) % 512,(m >>> 35) % 524288,
    (m >>> 54) % 2 == 1⟩

def lookupAt (blob i : Nat) : Nat := (blob >>> (32*i)) % 4294967296

end Compact3684.Chain.Packed
