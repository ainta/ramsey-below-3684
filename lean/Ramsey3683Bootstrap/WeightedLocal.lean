import Ramsey3683Bootstrap.WeightedParameters

/-!
Weighted one-vertex dichotomy. The proof handles empty children and negative
child excess explicitly; taking a root of a signed excess is not used.
-/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean

/-- Normalize failure of a weighted child. The exponent of its cardinality
ratio is 1 - theta/r, rather than the unweighted 1 - 1/r. -/
theorem weighted_contribution_le
    {d c α a N M θ : ℝ} {r : ℕ}
    (hr : 0 < r) (hθ : 0 < θ) (hθr : θ < (r : ℝ))
    (hd : 0 < d) (hc : 0 < c) (hα : 0 < α) (hN : 0 < N) (hM : 0 ≤ M)
    (hfail : ¬ (0 ≤ a ∧ c * α ^ r * N ^ θ ≤ d * a ^ r * M ^ θ)) :
    d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) ≤
      c ^ ((r : ℝ)⁻¹) * (M / N) ^ (1 - θ * (r : ℝ)⁻¹) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hi : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hθi : θ * (r : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hrR]
    exact hθr
  have hs : 0 < 1 - θ * (r : ℝ)⁻¹ := sub_pos.mpr hθi
  have hu0 : 0 ≤ M / N := div_nonneg hM hN.le
  by_cases ha : 0 ≤ a
  · by_cases hz : M = 0
    · subst M
      simp [Real.zero_rpow hs.ne']
    have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
    have hu : 0 < M / N := div_pos hMp hN
    have hstrict : d * a ^ r * M ^ θ < c * α ^ r * N ^ θ :=
      lt_of_not_ge (fun h => hfail ⟨ha, h⟩)
    have hden : 0 < α ^ r * N ^ θ :=
      mul_pos (pow_pos hα r) (Real.rpow_pos_of_pos hN θ)
    have hnorm : d * (a / α) ^ r * (M / N) ^ θ < c := by
      calc
        d * (a / α) ^ r * (M / N) ^ θ =
            (d * a ^ r * M ^ θ) / (α ^ r * N ^ θ) := by
          rw [div_pow, Real.div_rpow hM hN.le]
          field_simp [hα.ne', (Real.rpow_pos_of_pos hN θ).ne']
        _ < (c * α ^ r * N ^ θ) / (α ^ r * N ^ θ) :=
          div_lt_div_of_pos_right hstrict hden
        _ = c := by field_simp
    let A := d ^ ((r : ℝ)⁻¹) * (a / α) *
      (M / N) ^ (θ * (r : ℝ)⁻¹)
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hd.le _) (div_nonneg ha hα.le))
        (Real.rpow_nonneg hu0 _)
    have hratioPow : ((M / N) ^ (θ * (r : ℝ)⁻¹)) ^ r = (M / N) ^ θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0]
      congr 1
      field_simp
    have hAr : A ^ r < c := by
      dsimp [A]
      rw [mul_pow, mul_pow, Real.rpow_inv_natCast_pow hd.le hr.ne', hratioPow]
      exact hnorm
    have hroot : A ≤ c ^ ((r : ℝ)⁻¹) := by
      apply (Real.le_rpow_inv_iff_of_pos hA hc.le hrR).2
      rw [Real.rpow_natCast]
      exact hAr.le
    have hm := mul_le_mul_of_nonneg_right hroot
      (Real.rpow_nonneg hu0 (1 - θ * (r : ℝ)⁻¹))
    have hcombine : (M / N) ^ (θ * (r : ℝ)⁻¹) *
        (M / N) ^ (1 - θ * (r : ℝ)⁻¹) = M / N := by
      rw [← Real.rpow_add hu]
      have he : θ * (r : ℝ)⁻¹ + (1 - θ * (r : ℝ)⁻¹) = 1 := by ring
      rw [he, Real.rpow_one]
    calc
      d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) =
          A * (M / N) ^ (1 - θ * (r : ℝ)⁻¹) := by
        dsimp [A]
        rw [mul_assoc (d ^ ((r : ℝ)⁻¹) * (a / α)), hcombine]
      _ ≤ c ^ ((r : ℝ)⁻¹) * (M / N) ^ (1 - θ * (r : ℝ)⁻¹) := hm
  · have hneg : a < 0 := lt_of_not_ge ha
    have hl : d ^ ((r : ℝ)⁻¹) * (a / α) * (M / N) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hd.le _)
          (div_nonpos_of_nonpos_of_nonneg hneg.le hα.le)) hu0
    exact hl.trans (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg hu0 _))

/-- A fully numerical weighted red/blue alternative. The hypotheses are
finite inequalities on six real variables, not assumptions about graphs. -/
theorem weightedLocalDichotomy
    {x μ d θ ε β N R B α αR αB : ℝ} {r : ℕ}
    (hr : 0 < r) (hθ : 0 < θ) (hθr : θ < (r : ℝ))
    (hx : 0 < x) (hμ : 0 < μ) (hd : 0 < d)
    (hμβ : μ ≤ β) (hβ : β < 1)
    (hcap : β ≤ μ / (x ^ θ⁻¹ + μ))
    (hcritical : x ^ ((r : ℝ)⁻¹) * (1 - μ) ^ (1 - θ * (r : ℝ)⁻¹) + β + ε <
      d ^ ((r : ℝ)⁻¹))
    (hN : 0 < N) (hα : 0 < α)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hRB : R + B ≤ N) (hblue : B ≤ β * N)
    (hmoment : α * N ≤ αR * R + αB * B + 1)
    (herror : d ^ ((r : ℝ)⁻¹) / (α * N) ≤ ε) :
    (0 ≤ αR ∧ x * α ^ r * N ^ θ ≤ d * αR ^ r * R ^ θ) ∨
    (0 ≤ αB ∧ μ ^ θ * α ^ r * N ^ θ ≤ d * αB ^ r * B ^ θ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hi : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hθi : θ * (r : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hrR]
    exact hθr
  have hu : 0 ≤ R / N := div_nonneg hR hN.le
  have hv : 0 ≤ B / N := div_nonneg hB hN.le
  have huv : R / N + B / N ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hN).2 hRB
  have hvβ : B / N ≤ β := (div_le_iff₀ hN).2 hblue
  have hp := weightedProfile_le hx hμ hθ hi hθi hμβ hβ hcap hu hv huv hvβ
  by_contra hf
  have hrf : ¬ (0 ≤ αR ∧ x * α ^ r * N ^ θ ≤ d * αR ^ r * R ^ θ) :=
    fun h => hf (Or.inl h)
  have hbf : ¬ (0 ≤ αB ∧ μ ^ θ * α ^ r * N ^ θ ≤ d * αB ^ r * B ^ θ) :=
    fun h => hf (Or.inr h)
  have hred := weighted_contribution_le hr hθ hθr hd hx hα hN hR hrf
  have hblue' := weighted_contribution_le hr hθ hθr hd
    (Real.rpow_pos_of_pos hμ θ) hα hN hB hbf
  rw [← Real.rpow_mul hμ.le] at hblue'
  have hn : 1 ≤ (αR / α) * (R / N) + (αB / α) * (B / N) + 1 / (α * N) := by
    have hid : (αR / α) * (R / N) + (αB / α) * (B / N) + 1 / (α * N) =
        (αR * R + αB * B + 1) / (α * N) := by field_simp
    rw [hid]
    exact (le_div_iff₀ (mul_pos hα hN)).2 (by simpa using hmoment)
  have hmul := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hd.le ((r : ℝ)⁻¹))
  have hrootLower : d ^ ((r : ℝ)⁻¹) ≤
      x ^ ((r : ℝ)⁻¹) * (R / N) ^ (1 - θ * (r : ℝ)⁻¹) +
      μ ^ (θ * (r : ℝ)⁻¹) * (B / N) ^ (1 - θ * (r : ℝ)⁻¹) +
      d ^ ((r : ℝ)⁻¹) / (α * N) := by
    calc
      d ^ ((r : ℝ)⁻¹) ≤ d ^ ((r : ℝ)⁻¹) *
          ((αR / α) * (R / N) + (αB / α) * (B / N) + 1 / (α * N)) := by
        simpa using hmul
      _ = d ^ ((r : ℝ)⁻¹) * (αR / α) * (R / N) +
          d ^ ((r : ℝ)⁻¹) * (αB / α) * (B / N) + d ^ ((r : ℝ)⁻¹) / (α * N) := by ring
      _ ≤ _ := add_le_add (add_le_add hred hblue') le_rfl
  have hup := add_le_add hp herror
  exact (not_lt_of_ge (hrootLower.trans hup)) hcritical

end Ramsey3683Bootstrap
