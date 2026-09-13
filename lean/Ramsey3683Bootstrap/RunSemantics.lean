import Ramsey3683Bootstrap.Certificate

/-! Semantic composition of compressed continuation runs. The proof length
is independent of the number of integer graph steps and path references. -/
set_option autoImplicit false
namespace Compact3684.Certificate
open Ramsey3683Bootstrap

def Continuation (N lo hi : Nat) (u v : ℝ) : Prop :=
  (∀ j : Nat, ∀ w p : ℝ, 0 < w → GridCandidate.{0} N j lo u w p →
    GridCandidate.{0} N j hi v w p) ∧
  (GridUnconditional.{0} N lo u → GridUnconditional.{0} N hi v)

theorem Continuation.refl (N i : Nat) (u : ℝ) : Continuation N i i u u :=
  ⟨fun _ _ _ _ h => h,fun h => h⟩

theorem Continuation.trans {N lo mid hi : Nat} {u v w : ℝ}
    (h₁ : Continuation N lo mid u v) (h₂ : Continuation N mid hi v w) :
    Continuation N lo hi u w :=
  ⟨fun j z p hz h => h₂.1 j z p hz (h₁.1 j z p hz h),fun h => h₂.2 (h₁.2 h)⟩

theorem Continuation.chain (N count : Nat) (row : Nat → Nat) (value : Nat → ℝ)
    (h : ∀ i, i < count → Continuation N (row (i+1)) (row i) (value (i+1)) (value i)) :
    Continuation N (row count) (row 0) (value count) (value 0) := by
  induction count generalizing row value with
  | zero => exact Continuation.refl _ _ _
  | succ count ih =>
    have ht := ih (fun i => row (i+1)) (fun i => value (i+1))
      (fun i hi => h (i+1) (by omega))
    exact ht.trans (h 0 (by omega))

theorem exponent_pos {N : Nat} (hN : 0 < N) {z : Int} (hz : 0 < z) :
    0 < exponent N z := div_pos (by exact_mod_cast hz) (valueScale_pos hN)

theorem exponent_lt {N : Nat} (hN : 0 < N) {x y : Int} (hxy : x < y) :
    exponent N x < exponent N y :=
  (div_lt_div_iff_of_pos_right (valueScale_pos hN)).mpr (by exact_mod_cast hxy)

theorem exponent_add_cost {N : Nat} (hN : 0 < N) (x cost : Int) :
    exponent N (x+cost*1000000000000000000) = exponent N x+scalar cost/(N : ℝ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [exponent,scalar,valueScale,unit,Log18.scale,
    Int.cast_add,Int.cast_mul,Int.cast_natCast]
  norm_num
  field_simp
  <;> ring

/-- A range maximum and cost prefixes justify a whole compressed run.
Every referenced density is an actual graph theorem, not an arithmetic tag. -/
theorem continuation_of_range {N lo hi : Nat} (hN : 0 < N)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (pref floor cost : Nat → Int) (density : Nat → ℝ)
    {x maximum : Int}
    (hstep : ∀ i, lo ≤ i → i ≤ hi → pref i = pref (i-1)+cost i*1000000000000000000)
    (hcost : ∀ i, lo ≤ i → i ≤ hi → 0 < cost i)
    (hq : ∀ i, lo ≤ i → i ≤ hi → density i < 1)
    (hblue : ∀ i, lo ≤ i → i ≤ hi → 0 < scalar (cost i)+Real.log (1-density i))
    (hrange : RangeBound floor pref lo hi maximum)
    (hsize : pref hi+maximum < x)
    (hstart : pref hi-pref (lo-1) < x)
    (hd : ∀ i, lo ≤ i → i ≤ hi → GridDensity.{0} N i (exponent N (floor i)) (density i)) :
    Continuation N (lo-1) hi (exponent N (x-pref hi+pref (lo-1))) (exponent N x) := by
  let E := fun i => exponent N (x-pref hi+pref i)
  have hlow : lo-1 ≤ hi := by omega
  have hpos : ∀ i, lo-1 ≤ i → i ≤ hi → 0 < E i := by
    intro i hli hihi
    have hp : pref (lo-1) ≤ pref i := increasing_range_le (f := pref) (lo := lo-1) (hi := hi)
      (fun j hlj hjh => by
        have hs := hstep (j+1) (by omega) (by omega)
        have hc := hcost (j+1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hs
        omega) i hli hihi
    exact exponent_pos hN (by omega)
  have hsz := range_valid_of_bound hrange hsize
  have hsize' : ∀ i, lo-1 < i → i ≤ hi → exponent N (floor i) < E (i-1) := by
    intro i hli hihi
    exact exponent_lt hN (by have h := hsz i (by omega) hihi; omega)
  have hstep' : ∀ i, lo-1 < i → i ≤ hi → E i = E (i-1)+scalar (cost i)/(N : ℝ) := by
    intro i hli hihi
    dsimp [E]
    rw [hstep i (by omega) hihi]
    rw [show x-pref hi+(pref (i-1)+cost i*1000000000000000000) =
      (x-pref hi+pref (i-1))+cost i*1000000000000000000 by omega]
    exact exponent_add_cost hN _ _
  have hcost' : ∀ i, lo-1 < i → i ≤ hi → 0 < scalar (cost i) :=
    fun i hli hihi => scalar_pos (hcost i (by omega) hihi)
  have hq' : ∀ i, lo-1 < i → i ≤ hi → density i < 1 := fun i hli hihi => hq i (by omega) hihi
  have hblue' : ∀ i, lo-1 < i → i ≤ hi → 0 < scalar (cost i)+Real.log (1-density i) :=
    fun i hli hihi => hblue i (by omega) hihi
  have hd' : ∀ i, lo-1 < i → i ≤ hi → GridDensity.{0} N i (exponent N (floor i)) (density i) :=
    fun i hli hihi => hd i (by omega) hihi
  have hend : E hi = exponent N x := by dsimp [E]; congr 1; omega
  constructor
  · intro j w p hw hbase
    have h := GridCandidate.path E (fun i => scalar (cost i)) (fun i => exponent N (floor i)) density
      hN hlow hw hpos hcost' hq' hblue' hsize' hstep' hd' hbase
    exact hend ▸ h
  · intro hbase
    have h := GridUnconditional.path E (fun i => scalar (cost i)) (fun i => exponent N (floor i)) density
      hN hlow hpos hcost' hq' hblue' hsize' hstep' hd' hbase
    exact hend ▸ h.1

#print axioms continuation_of_range
end Compact3684.Certificate
