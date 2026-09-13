import Ramsey3683Bootstrap.WeightedEngine

/-! Graph-independent weighted schedules. The logarithmic spine and its
subexponential Ramsey losses are reused from the pinned upstream library. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology

/-- Separate the moment exponent from the larger integer needed to pay
for a possibly small positive weight in the blue-book step. -/
theorem exists_weightedScheduleExponent {θ : ℝ} (hθ : 0 < θ) (r : ℕ) :
    ∃ R : ℕ, 0 < R ∧ r ≤ R ∧ (r : ℝ) ≤ (R : ℝ) * θ := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max (r : ℝ) ((r : ℝ) / θ))
  have hrR : (r : ℝ) < R := (le_max_left _ _).trans_lt hR
  have hdiv : (r : ℝ) / θ < R := (le_max_right _ _).trans_lt hR
  refine ⟨R, ?_, ?_, ((div_lt_iff₀ hθ).mp hdiv).le⟩
  · have : r < R := by exact_mod_cast hrR
    omega
  · exact_mod_cast hrR.le

/-- Weighted blue gain obtained by raising the existing logarithmic-spine
estimate to theta. This is a single analytic proof, not graph enumeration. -/
theorem weightedSpine_gain {e η μ β θ : ℝ} {r R n : ℕ}
    (he : e ∈ Ioo (0 : ℝ) 1) (heη : e ≤ η)
    (hμ : 0 < μ) (hβ : 0 < β) (hθ : 0 < θ)
    (hrθ : (r : ℝ) ≤ (R : ℝ) * θ)
    (hratio : (1 + e) * μ ≤ β) (hn : 0 < n) :
    (μ ^ θ) ^ bookSpineSize e R n ≤
      (η / (n : ℝ) ^ 2) ^ r *
        (β ^ bookSpineSize e R n / 2) ^ θ := by
  let b := bookSpineSize e R n
  let a := (n : ℝ) ^ 2 / e
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have he0 := he.1
  have he1 := he.2
  have hbase : 0 < 1 + e := by linarith
  have heηpos : 0 < η := he.1.trans_le heη
  have ha : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ he.1]
    nlinarith
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hg : 2 * a ^ R ≤ (1 + e) ^ b := bookSpineSize_gain he hn
  have hgp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * a ^ R) hg hθ.le
  have haR : (a ^ R) ^ θ = a ^ ((R : ℝ) * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hap.le]
  have harg : (n : ℝ) ^ 2 / η ≤ a := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) he.1 heη
  have hpow : ((n : ℝ) ^ 2 / η) ^ r ≤ (a ^ R) ^ θ := by
    calc
      ((n : ℝ) ^ 2 / η) ^ r ≤ a ^ r :=
        pow_le_pow_left₀ (by positivity) harg r
      _ ≤ a ^ ((R : ℝ) * θ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le ha hrθ
      _ = (a ^ R) ^ θ := haR.symm
  have hratioPow : (1 + e) ^ b * μ ^ b ≤ β ^ b := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hratio b
  have hratioTheta := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ (1 + e) ^ b * μ ^ b) hratioPow hθ.le
  have hμb : (μ ^ θ) ^ b = (μ ^ b) ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le,
      ← Real.rpow_mul hμ.le]
    congr 1
    ring
  have hgain : 2 ^ θ * (((n : ℝ) ^ 2 / η) ^ r) * (μ ^ b) ^ θ ≤ (β ^ b) ^ θ := by
    calc
      _ ≤ 2 ^ θ * (a ^ R) ^ θ * (μ ^ b) ^ θ := by gcongr
      _ = (2 * a ^ R) ^ θ * (μ ^ b) ^ θ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg hap.le R)]
      _ ≤ ((1 + e) ^ b) ^ θ * (μ ^ b) ^ θ := by gcongr
      _ = ((1 + e) ^ b * μ ^ b) ^ θ := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (1 + e) ^ b) (pow_nonneg hμ.le b)]
      _ ≤ (β ^ b) ^ θ := hratioTheta
  have htwo : (0 : ℝ) < 2 ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hrecip : (η / (n : ℝ) ^ 2) ^ r * ((n : ℝ) ^ 2 / η) ^ r = 1 := by
    rw [← mul_pow]
    have : η / (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 / η) = 1 := by
      field_simp
    rw [this, one_pow]
  rw [hμb, Real.div_rpow (pow_nonneg hβ.le b) (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← mul_div_assoc, le_div_iff₀ htwo]
  have h := mul_le_mul_of_nonneg_left hgain
    (pow_nonneg (div_nonneg heηpos.le (sq_nonneg (n : ℝ))) r)
  calc
    (μ ^ b) ^ θ * 2 ^ θ =
        (η / (n : ℝ) ^ 2) ^ r *
          (2 ^ θ * ((n : ℝ) ^ 2 / η) ^ r * (μ ^ b) ^ θ) := by
      calc
        _ = ((η / (n : ℝ) ^ 2) ^ r * ((n : ℝ) ^ 2 / η) ^ r) *
            ((μ ^ b) ^ θ * 2 ^ θ) := by rw [hrecip, one_mul]
        _ = _ := by ring
    _ ≤ (η / (n : ℝ) ^ 2) ^ r * (β ^ b) ^ θ := h

/-- Cardinality growth is paid for coordinatewise. The exponential base
for the left set is raised to theta, but the target remains a product of
ordinary natural powers. -/
theorem weightedTarget_growth {a x y u xR yR : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hy : 0 < y) (hu : 0 < u)
    (hxR : 0 < xR) (hyR : 0 < yR)
    (hxs : a * x ≤ xR) (hys : a * y ≤ yR) (hus : a * u ≤ 1)
    (k t ℓ : ℕ) :
    a ^ (k + t + ℓ) * ((xR⁻¹) ^ k * (yR⁻¹) ^ ℓ) ≤
      bookTarget x y u ℓ k t := by
  have hxscale : a * xR⁻¹ ≤ x⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hxR hx]
    simpa using hxs
  have hyscale : a * yR⁻¹ ≤ y⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hyR hy]
    simpa using hys
  have huscale : a ≤ u⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hu]
    exact hus
  have hk := pow_le_pow_left₀ (mul_nonneg ha (inv_nonneg.mpr hxR.le)) hxscale k
  have hl := pow_le_pow_left₀ (mul_nonneg ha (inv_nonneg.mpr hyR.le)) hyscale ℓ
  have ht := pow_le_pow_left₀ ha huscale t
  rw [bookTarget]
  calc
    a ^ (k + t + ℓ) * ((xR⁻¹) ^ k * (yR⁻¹) ^ ℓ) =
        (a * xR⁻¹) ^ k * (a * yR⁻¹) ^ ℓ * a ^ t := by
      simp only [pow_add, mul_pow]
      ring
    _ ≤ (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (u⁻¹) ^ t := by
      exact mul_le_mul (mul_le_mul hk hl (by positivity) (by positivity)) ht
        (pow_nonneg ha t) (by positivity)

theorem weighted_left_large {e θ x y u xR yR NX NY α : ℝ} {r n k t ℓ : ℕ}
    (he : 0 < e) (hθ : 0 < θ)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u)
    (hxR : 0 < xR) (hyR : 0 < yR)
    (hxs : (1 + e) ^ θ * x ≤ xR)
    (hys : (1 + e) ^ θ * y ≤ yR)
    (hus : (1 + e) ^ θ * u ≤ 1)
    (hn : n = k + t) (hNX : 0 < NX) (hNY : 0 < NY)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmoment : bookTarget x y u ℓ k t ≤ α ^ r * NX ^ θ * NY)
    (hY : NY < (xR⁻¹) ^ k * (yR⁻¹) ^ ℓ) :
    (bookMinimumLeftSize e ℓ n : ℝ) ≤ NX := by
  have hbase : 0 < 1 + e := by linarith
  have hscale := weightedTarget_growth (Real.rpow_nonneg hbase.le θ)
    hx hy hu hxR hyR hxs hys hus k t ℓ
  have hαpow : α ^ r ≤ 1 := pow_le_one₀ hα0 hα1
  have htarget : bookTarget x y u ℓ k t ≤ NX ^ θ * NY := by
    calc
      _ ≤ α ^ r * NX ^ θ * NY := hmoment
      _ ≤ 1 * NX ^ θ * NY := by gcongr
      _ = NX ^ θ * NY := by ring
  have hpowid : ((1 + e) ^ θ) ^ (n + ℓ) = ((1 + e) ^ (n + ℓ)) ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le,
      ← Real.rpow_mul hbase.le]
    congr 1
    ring
  rw [← hn, hpowid] at hscale
  have hstrict : ((1 + e) ^ (n + ℓ)) ^ θ < NX ^ θ := by
    have h : ((1 + e) ^ (n + ℓ)) ^ θ * ((xR⁻¹) ^ k * (yR⁻¹) ^ ℓ) <
        NX ^ θ * ((xR⁻¹) ^ k * (yR⁻¹) ^ ℓ) :=
      hscale.trans_lt (htarget.trans_lt (mul_lt_mul_of_pos_left hY
        (Real.rpow_pos_of_pos hNX θ)))
    exact (mul_lt_mul_iff_left₀ (by positivity : (0 : ℝ) <
      (xR⁻¹) ^ k * (yR⁻¹) ^ ℓ)).mp h
  have hENX : (1 + e) ^ (n + ℓ) < NX := by
    by_contra hf
    have hc := Real.rpow_le_rpow hNX.le (le_of_not_gt hf) hθ.le
    exact (not_lt_of_ge hc) hstrict
  exact (Nat.floor_le (pow_nonneg hbase.le _)).trans hENX.le

end Ramsey3683Bootstrap
