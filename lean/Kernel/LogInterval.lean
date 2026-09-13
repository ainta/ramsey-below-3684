import Kernel.Log18
import RamseyLean.Analysis.FixedPointInterval

set_option autoImplicit false
namespace Compact3684.Log18
open RamseyLean.FixedPointInterval (cast_ediv_le_div div_le_cast_ceil)

noncomputable def value (z : Int) : ℝ := (z : ℝ) / (q : ℝ)
def Contains (a : Interval) (x : ℝ) : Prop := value a.1 ≤ x ∧ x ≤ value a.2
def Nonneg (a : Interval) : Prop := 0 ≤ a.1

theorem q_pos : (0 : Int) < q := by norm_num [q]
theorem q_pos_real : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q_pos

@[simp] theorem value_add (a b : Int) : value (a+b) = value a + value b := by
  simp [value]; ring
@[simp] theorem value_mul_int (a k : Int) : value (k*a) = (k : ℝ) * value a := by
  simp [value]; ring
@[simp] theorem value_zero : value 0 = 0 := by simp [value]
theorem value_nonneg {a : Int} (ha : 0 ≤ a) : 0 ≤ value a := by
  exact div_nonneg (by exact_mod_cast ha) q_pos_real.le

theorem value_floor {a d : Int} (hd : 0 < d) :
    value (a/d) ≤ value a / (d : ℝ) := by
  have h := div_le_div_of_nonneg_right (cast_ediv_le_div (a := a) hd) q_pos_real.le
  simpa only [value, div_right_comm] using h
theorem value_ceil {a d : Int} (hd : 0 < d) :
    value a / (d : ℝ) ≤ value (ceilDiv a d) := by
  have h := div_le_div_of_nonneg_right (div_le_cast_ceil (a := a) hd) q_pos_real.le
  simpa only [value, ceilDiv, div_right_comm] using h

theorem rat_contains {n d : Int} (hd : 0 < d) : Contains (rat n d) ((n : ℝ) / d) := by
  have he : value (n*q) / (d : ℝ) = (n : ℝ) / d := by
    simp [value, q_pos_real.ne']
  exact ⟨(value_floor hd).trans_eq he, he.symm.trans_le (value_ceil hd)⟩
theorem rat_nonneg {n d : Int} (hn : 0 ≤ n) (hd : 0 < d) : Nonneg (rat n d) := by
  exact Int.ediv_nonneg (mul_nonneg hn q_pos.le) hd.le

theorem Contains.plus {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (plus a b) (x+y) := by
  simpa only [Contains, Compact3684.Log18.plus, value_add] using
    And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)
theorem Nonneg.plus {a b : Interval} (ha : Nonneg a) (hb : Nonneg b) :
    Nonneg (plus a b) := add_nonneg ha hb

theorem Contains.divide {a : Interval} {x : ℝ} {d : Int}
    (ha : Contains a x) (hd : 0 < d) : Contains (divide a d) (x / (d : ℝ)) := by
  have hdr : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
  exact ⟨(value_floor hd).trans (div_le_div_of_nonneg_right ha.1 hdr),
    (div_le_div_of_nonneg_right ha.2 hdr).trans (value_ceil hd)⟩
theorem Nonneg.divide {a : Interval} {d : Int} (ha : Nonneg a) (hd : 0 < d) :
    Nonneg (divide a d) := Int.ediv_nonneg ha hd.le

theorem value_mul_scaled (a b : Int) : value (a*b) / (q : ℝ) = value a * value b := by
  simp [value]; ring

theorem Contains.timesPos {a b : Interval} {x y : ℝ}
    (ha : Contains a x) (hb : Contains b y) (hNa : Nonneg a) (hNb : Nonneg b) :
    Contains (timesPos a b) (x*y) := by
  have hax : 0 ≤ x := (value_nonneg hNa).trans ha.1
  have hby : 0 ≤ y := (value_nonneg hNb).trans hb.1
  constructor
  · change value (a.1*b.1/q) ≤ x*y
    apply (value_floor q_pos).trans
    rw [value_mul_scaled]
    exact mul_le_mul ha.1 hb.1 (value_nonneg hNb) hax
  · change x*y ≤ value (ceilDiv (a.2*b.2) q)
    apply le_trans _ (value_ceil q_pos)
    rw [value_mul_scaled]
    exact mul_le_mul ha.2 hb.2 hby (hax.trans ha.2)
theorem Nonneg.timesPos {a b : Interval} (ha : Nonneg a) (hb : Nonneg b) :
    Nonneg (timesPos a b) := Int.ediv_nonneg (mul_nonneg ha hb) q_pos.le

theorem Contains.timesInt {a : Interval} {x : ℝ} (ha : Contains a x) (k : Int) :
    Contains (timesInt a k) ((k : ℝ)*x) := by
  unfold Compact3684.Log18.timesInt
  split_ifs with hk
  · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
    simpa only [Contains, value_mul_int] using
      And.intro (mul_le_mul_of_nonneg_left ha.1 hkr) (mul_le_mul_of_nonneg_left ha.2 hkr)
  · have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hk)
    simpa only [Contains, value_mul_int] using
      And.intro (mul_le_mul_of_nonpos_left ha.2 hkr) (mul_le_mul_of_nonpos_left ha.1 hkr)

noncomputable def poly (u : ℝ) (j : Nat) : ℝ :=
  ∑ i ∈ Finset.range j, u ^ (2*i+1) / (2*i+1)

theorem series_contains {u L : ℝ} {u2 : Interval}
    (hu2 : Contains u2 (u^2)) (hNu2 : Nonneg u2)
    (n j : Nat) (w total : Interval)
    (hw : Contains w (u^(2*j+1))) (hNw : Nonneg w) (ht : Contains total (poly u j))
    (hlo : 2 * poly u (j+n) ≤ L) (hhi : L ≤ 2 * poly u (j+n) + value 1) :
    Contains (series u2 n j w total) L := by
  induction n generalizing j w total with
  | zero =>
    simp only [Nat.add_zero] at hlo hhi
    change value (2*total.1) ≤ L ∧ L ≤ value (2*total.2+1)
    simp only [value_add, value_mul_int, Int.cast_ofNat]
    constructor <;> linarith [ht.1, ht.2]
  | succ n ih =>
    have hd : (0 : Int) < 2*(j : Int)+1 := by omega
    have hdiv := hw.divide hd
    have hadd := ht.plus hdiv
    have htotal : Contains (plus total (divide w (2*j+1))) (poly u (j+1)) := by
      simpa only [poly, Finset.sum_range_succ, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast, Int.cast_one] using hadd
    have hnext : Contains (timesPos w u2) (u^(2*(j+1)+1)) := by
      have he : 2*(j+1)+1 = (2*j+1)+2 := by omega
      rw [he, pow_add]
      exact hw.timesPos hu2 hNw hNu2
    apply ih (j+1) (timesPos w u2) (plus total (divide w (2*j+1))) hnext
      (hNw.timesPos hNu2) htotal
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlo
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi

theorem reduced_contains {n d : Int} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2*d) :
    Contains (reduced n d) (Real.log ((n : ℝ)/d)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hnr : (d : ℝ) ≤ n := by exact_mod_cast hlo
  have hnr' : (n : ℝ) ≤ 2*d := by exact_mod_cast hhi
  have hsum : (0 : ℝ) < (n : ℝ)+d := by linarith
  have hsumI : (0 : Int) < n+d := by omega
  let u : ℝ := ((n : ℝ)-d)/((n : ℝ)+d)
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hnr) hsum.le
  have hu13 : u ≤ 1/3 := by
    dsimp [u]
    rw [div_le_iff₀ hsum]
    linarith
  have hu1 : u < 1 := by linarith
  have heq : (1+u)/(1-u) = (n : ℝ)/d := by
    dsimp [u]
    field_simp [hdr.ne', hsum.ne']
    <;> ring
  have hlow := Real.sum_range_le_log_div hu0 hu1 20
  have hupp := Real.log_div_le_sum_range_add hu0 hu1 20
  rw [heq] at hlow hupp
  have hp41 : u^41 ≤ (1/3 : ℝ)^41 := pow_le_pow_left₀ hu0 hu13 41
  have hp2 : u^2 ≤ (1/3 : ℝ)^2 := pow_le_pow_left₀ hu0 hu13 2
  have htail : 2 * (u^41 / (1-u^2)) ≤ value 1 := by
    calc
      _ ≤ 2 * ((1/3 : ℝ)^41 / (1-(1/3 : ℝ)^2)) := by
        gcongr
      _ ≤ value 1 := by norm_num [value, q]
  have hr : Contains (rat (n-d) (n+d)) u := by
    simpa only [Int.cast_sub, Int.cast_add] using rat_contains (n := n-d) hsumI
  have hNr : Nonneg (rat (n-d) (n+d)) := rat_nonneg (sub_nonneg.mpr hlo) hsumI
  apply series_contains (u := u) (by simpa only [pow_two] using hr.timesPos hr hNr hNr)
    (hNr.timesPos hNr) 20 0
    (rat (n-d) (n+d)) (0,0)
  · simpa using hr
  · exact hNr
  · simp [Contains, poly, value_zero]
  · change 2 * poly u 20 ≤ Real.log ((n : ℝ)/d)
    change poly u 20 ≤ 1/2 * Real.log ((n : ℝ)/d) at hlow
    linarith
  · change Real.log ((n : ℝ)/d) ≤ 2 * poly u 20 + value 1
    change 1/2 * Real.log ((n : ℝ)/d) ≤ poly u 20 + u^41/(1-u^2) at hupp
    linarith

theorem normalize_sound (fuel : Nat) {n d k nn dd kk : Int}
    (hn : 0 < n) (hd : 0 < d) (h : normalize fuel n d k = some (nn,dd,kk)) :
    0 < dd ∧ dd ≤ nn ∧ nn < 2*dd ∧
      Real.log ((n : ℝ)/d) + (k : ℝ)*Real.log 2 =
        Real.log ((nn : ℝ)/dd) + (kk : ℝ)*Real.log 2 := by
  induction fuel generalizing n d k with
  | zero => simp [normalize] at h
  | succ fuel ih =>
    simp only [normalize] at h
    split_ifs at h with hlow hhigh
    · obtain ⟨hdd, hnd, hnd', he⟩ := ih (by omega : 0 < 2*n) hd h
      refine ⟨hdd, hnd, hnd', ?_⟩
      rw [← he]
      have hratio : (n : ℝ)/d ≠ 0 := div_ne_zero
        (by exact_mod_cast hn.ne') (by exact_mod_cast hd.ne')
      have hlog : Real.log (((2*n : Int) : ℝ)/d) = Real.log 2 + Real.log ((n : ℝ)/d) := by
        push_cast
        rw [mul_div_assoc, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hratio]
      rw [hlog]
      push_cast
      ring
    · obtain ⟨hdd, hnd, hnd', he⟩ := ih hn (by omega : 0 < 2*d) h
      refine ⟨hdd, hnd, hnd', ?_⟩
      rw [← he]
      have hratio : (n : ℝ)/d ≠ 0 := div_ne_zero
        (by exact_mod_cast hn.ne') (by exact_mod_cast hd.ne')
      have hlog : Real.log ((n : ℝ)/((2*d : Int) : ℝ)) =
          Real.log ((n : ℝ)/d) - Real.log 2 := by
        have heq : (n : ℝ)/((2*d : Int) : ℝ) = ((n : ℝ)/d)/2 := by push_cast; ring
        rw [heq, Real.log_div hratio (by norm_num : (2 : ℝ) ≠ 0)]
      rw [hlog]
      push_cast
      ring
    · cases Option.some.inj h
      exact ⟨hd, le_of_not_gt hlow, lt_of_not_ge hhigh, rfl⟩

theorem logTwoBounds_contains : Contains logTwoBounds (Real.log 2) := by
  have h := reduced_contains (n := 2) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  simpa only [logTwoBounds_correct, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- Soundness of the exact executable logarithm, including dyadic
normalization, directed integer rounding, and the analytic series tail. -/
theorem logarithm_contains {n d : Int} {a : Interval} (h : logarithm n d = some a) :
    Contains a (Real.log ((n : ℝ)/d)) := by
  unfold logarithm at h
  split_ifs at h with hbad
  have hn : 0 < n := by omega
  have hd : 0 < d := by omega
  cases hnorm : normalize 128 n d 0 with
  | none => simp only [hnorm] at h; contradiction
  | some result =>
    rcases result with ⟨nn,dd,k⟩
    simp only [hnorm, Option.some.injEq] at h
    rw [← h]
    obtain ⟨hdd,hnd,hnd',he⟩ := normalize_sound 128 hn hd hnorm
    have hc := (reduced_contains hdd hnd hnd'.le).plus (logTwoBounds_contains.timesInt k)
    rw [← he] at hc
    simpa only [Int.cast_zero, zero_mul, add_zero] using hc

theorem catalogGuard_sound (entry : CatalogEntry) (h : catalogGuard entry = true) :
    Contains (entry.lo,entry.hi) (Real.log ((entry.argument : ℝ)/scale)) := by
  unfold catalogGuard at h
  cases he : logarithm entry.argument scale with
  | none => simp only [he, Bool.false_eq_true] at h
  | some bounds =>
    simp only [he, decide_eq_true_eq] at h
    have hc := logarithm_contains he
    constructor
    · apply le_trans _ hc.1
      exact div_le_div_of_nonneg_right (by exact_mod_cast h.1) q_pos_real.le
    · apply le_trans hc.2
      exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) q_pos_real.le

theorem catalogAll_sound (entries : List CatalogEntry) (h : entries.all catalogGuard = true) :
    ∀ entry ∈ entries,
      Contains (entry.lo,entry.hi) (Real.log ((entry.argument : ℝ)/scale)) := by
  intro entry he
  exact catalogGuard_sound entry (List.all_eq_true.mp h entry he)

#print axioms catalogGuard_sound
end Compact3684.Log18
