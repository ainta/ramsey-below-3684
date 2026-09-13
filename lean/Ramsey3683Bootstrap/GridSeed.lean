import Ramsey3683Bootstrap.GridSemantics

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

theorem weighted_parameter_of_log_gap {a θ μ p : ℝ}
    (hμ : μ ∈ Ioo (0 : ℝ) 1) (hp : 0 < p)
    (hgap : 0 < (1 - μ) * (a + θ * Real.log (1 - μ)) + Real.log p) :
    Real.exp (-a) < p ^ (1 / (1 - μ)) * (1 - μ) ^ θ := by
  have hb : 0 < 1 - μ := sub_pos.mpr hμ.2
  have hlog : -a - θ * Real.log (1 - μ) < Real.log p / (1 - μ) := by
    rw [lt_div_iff₀ hb]
    nlinarith
  apply (Real.log_lt_log_iff (Real.exp_pos (-a))
    (mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hb _))).mp
  rw [Real.log_exp, Real.log_mul (Real.rpow_pos_of_pos hp _).ne'
    (Real.rpow_pos_of_pos hb _).ne', Real.log_rpow hp, Real.log_rpow hb]
  have he : 1 / (1 - μ) * Real.log p = Real.log p / (1 - μ) := by ring
  rw [he]
  linarith

theorem bookTarget_exp (a b θ : ℝ) {μ : ℝ} (hμ : 0 < μ) (k ℓ t : ℕ) :
    bookTarget (Real.exp (-a)) (Real.exp (-b)) (μ ^ θ) ℓ k t =
      Real.exp (a * k + b * ℓ - θ * Real.log μ * t) := by
  have hx : ((Real.exp (-a))⁻¹) ^ k = Real.exp (a * k) := by
    rw [← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hy : ((Real.exp (-b))⁻¹) ^ ℓ = Real.exp (b * ℓ) := by
    rw [← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hm : ((μ ^ θ)⁻¹) ^ t = Real.exp (-θ * Real.log μ * t) := by
    rw [Real.rpow_def_of_pos hμ, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  unfold bookTarget
  rw [hx, hy, hm, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- A weighted numerical seed is a graph-semantic seed. The input region
point is the actual upstream Ramsey region, not a certificate validity tag. -/
theorem gridCandidate_of_weighted_seed {N j i : ℕ} {u v a b θ μ p : ℝ}
    (hN : 0 < N) (hj : 0 < j) (hi : 0 < i) (hθ : 0 < θ)
    (hμ : μ ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hregion : (Real.exp (-a), Real.exp (-b)) ∈ asymptoticRegionInterior)
    (hdensity : 0 < (1 - μ) * (a + θ * Real.log (1 - μ)) + Real.log p)
    (hbudget : a + (j : ℝ) / N * b - θ * ((i : ℝ) / N) * Real.log μ < θ * u + v) :
    GridCandidate.{u} N j i u v p := by
  obtain ⟨L, hbook⟩ := isGood_of_density_weighted_card_product
    (Real.exp_pos (-a)) (Real.exp_pos (-b)) hμ hp hθ
    (weighted_parameter_of_log_gap hμ hp.1 hdensity) hregion
  intro ε hε
  filter_upwards [eventually_ge_atTop L, eventually_gt_atTop 0] with m hm hm0
  intro V instF instEq G instAdj X Y hcan hrow hX hY
  have hNm : (0 : ℝ) ≤ (N * m : ℕ) := Nat.cast_nonneg _
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hjm : L ≤ j * m := hm.trans (Nat.le_mul_of_pos_left m hj)
  apply hbook (Nat.mul_pos hN hm0) (Nat.mul_pos hj hm0) (Nat.mul_pos hi hm0) hjm hcan
    (redDensity_ge_of_rowFloor G hcan.left_nonempty hcan.right_nonempty hrow)
  change bookTarget (Real.exp (-a)) (Real.exp (-b)) (μ ^ θ) (j * m) (N * m) (i * m) ≤ _
  rw [bookTarget_exp a b θ hμ.1]
  have hs : a * (N * m : ℕ) + b * (j * m : ℕ) - θ * Real.log μ * (i * m : ℕ) ≤
      (N * m : ℕ) * (θ * u + v) := by
    calc
      _ = (N * m : ℕ) *
          (a + (j : ℝ) / N * b - θ * ((i : ℝ) / N) * Real.log μ) := by
        push_cast
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget.le hNm
  have hεgain : (N * m : ℕ) * (θ * u + v) ≤
      ((N * m : ℕ) * (u + ε)) * θ + (N * m : ℕ) * (v + ε) := by
    have hpos := mul_nonneg hNm (mul_nonneg hθ.le hε.le)
    have hpos' := mul_nonneg hNm hε.le
    nlinarith
  calc
    _ ≤ Real.exp (((N * m : ℕ) * (u + ε)) * θ + (N * m : ℕ) * (v + ε)) :=
      Real.exp_le_exp.mpr (hs.trans hεgain)
    _ = (Real.exp ((N * m : ℕ) * (u + ε))) ^ θ * Real.exp ((N * m : ℕ) * (v + ε)) := by
      rw [Real.exp_add, Real.exp_mul]
    _ ≤ (#X : ℝ) ^ θ * (#Y : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (Real.exp_pos _).le hX hθ.le) hY
        (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

#print axioms gridCandidate_of_weighted_seed
end Ramsey3683Bootstrap
