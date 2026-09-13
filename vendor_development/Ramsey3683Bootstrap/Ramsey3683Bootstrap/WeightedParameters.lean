import RamseyLean.BookInduction
import Mathlib.Tactic

/-!
The weighted limiting parameter and capped profile are reductions to the
existing GNNW calculus in the pinned bootstrap repository.
-/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology

noncomputable def weightedBookParameter (p μ θ : ℝ) (r : ℕ) : ℝ :=
  bookParameter p μ r * (1 - μ) ^ (θ - 1)

theorem weightedBookParameter_eq {p μ θ : ℝ} (hμ : μ < 1) (r : ℕ) :
    weightedBookParameter p μ θ r =
      (p ^ ((r : ℝ)⁻¹) - μ) ^ r * (1 - μ) ^ (θ - (r : ℝ)) := by
  have hb : 0 < 1 - μ := sub_pos.mpr hμ
  unfold weightedBookParameter bookParameter
  rw [mul_assoc, ← Real.rpow_add hb]
  congr 2
  ring

/-- No new limit calculation: multiply the upstream limit by a constant. -/
theorem tendsto_weightedBookParameter {p μ θ : ℝ}
    (hp : 0 < p) (hμ : μ < 1) :
    Tendsto (weightedBookParameter p μ θ) atTop
      (𝓝 (p ^ (1 / (1 - μ)) * (1 - μ) ^ θ)) := by
  have hb : 0 < 1 - μ := sub_pos.mpr hμ
  have hid : (1 - μ) * (1 - μ) ^ (θ - 1) = (1 - μ) ^ θ := by
    calc
      (1 - μ) * (1 - μ) ^ (θ - 1) =
          (1 - μ) ^ (1 : ℝ) * (1 - μ) ^ (θ - 1) := by rw [Real.rpow_one]
      _ = (1 - μ) ^ (1 + (θ - 1)) := (Real.rpow_add hb _ _).symm
      _ = (1 - μ) ^ θ := by congr 1 <;> ring
  have h := (tendsto_bookParameter hp hμ).mul_const ((1 - μ) ^ (θ - 1))
  simpa only [weightedBookParameter, mul_assoc, hid] using h

/-- A natural moment exponent can simultaneously exceed theta and realize
all the strict weighted parameter slack. -/
theorem exists_weightedBookExponent {p μ θ x : ℝ}
    (hp : 0 < p) (hμ : μ < 1)
    (hx : x < p ^ (1 / (1 - μ)) * (1 - μ) ^ θ) :
    ∃ r : ℕ, 2 ≤ r ∧ θ < (r : ℝ) ∧ μ < p ^ ((r : ℝ)⁻¹) ∧
      x < weightedBookParameter p μ θ r := by
  have hroot : Tendsto (fun r : ℕ => p ^ ((r : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow hp.ne').tendsto.comp
      tendsto_inv_atTop_nhds_zero_nat
    convert h using 1 <;> simp [Function.comp_def]
  have hm : ∀ᶠ r : ℕ in atTop, μ < p ^ ((r : ℝ)⁻¹) :=
    hroot.eventually (Ioi_mem_nhds hμ)
  have hx' : ∀ᶠ r : ℕ in atTop, x < weightedBookParameter p μ θ r :=
    (tendsto_weightedBookParameter (θ := θ) hp hμ).eventually (Ioi_mem_nhds hx)
  have hθ : ∀ᶠ r : ℕ in atTop, θ < (r : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈θ⌉₊ + 1)] with r hr
    have hr' : (⌈θ⌉₊ : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hc := Nat.le_ceil θ
    linarith
  exact ((eventually_ge_atTop (2 : ℕ)).and (hθ.and (hm.and hx'))).exists

/-- The weighted power-profile expression is exactly an upstream profile
with the first parameter replaced by its theta-th root. -/
theorem weightedProfile_eq_bookProfile
    {x θ ρ μ z : ℝ} (hx : 0 < x) (hθ : θ ≠ 0) :
    x ^ ρ * (1 - z) ^ (1 - θ * ρ) + μ ^ (θ * ρ) * z ^ (1 - θ * ρ) =
      bookProfile (x ^ θ⁻¹) μ (1 - θ * ρ) z := by
  have he : θ⁻¹ * (1 - (1 - θ * ρ)) = ρ := by field_simp
  unfold bookProfile
  rw [← Real.rpow_mul hx.le, he]
  have he' : 1 - (1 - θ * ρ) = θ * ρ := by ring
  rw [he']

theorem weightedProfile_le {x μ θ ρ β u v : ℝ}
    (hx : 0 < x) (hμ : 0 < μ) (hθ : 0 < θ)
    (hρ : 0 < ρ) (hθρ : θ * ρ < 1)
    (hμβ : μ ≤ β) (hβ : β < 1)
    (hcap : β ≤ μ / (x ^ θ⁻¹ + μ))
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) (hvβ : v ≤ β) :
    x ^ ρ * u ^ (1 - θ * ρ) + μ ^ (θ * ρ) * v ^ (1 - θ * ρ) ≤
      x ^ ρ * (1 - μ) ^ (1 - θ * ρ) + β := by
  have hs0 : 0 < 1 - θ * ρ := sub_pos.mpr hθρ
  have hs1 : 1 - θ * ρ < 1 := by nlinarith
  have h := bookProfile_le (Real.rpow_pos_of_pos hx θ⁻¹) hμ hs0 hs1
    hμβ hβ hcap hu hv huv hvβ
  have he : θ⁻¹ * (1 - (1 - θ * ρ)) = ρ := by field_simp
  have he' : 1 - (1 - θ * ρ) = θ * ρ := by ring
  simpa only [← Real.rpow_mul hx.le, he, he'] using h

/-- Convert the strict weighted parameter to the root inequality needed by
local induction. The natural power is retained for moment monotonicity. -/
theorem weighted_root_gap {x p μ θ : ℝ} {r : ℕ}
    (hx : 0 < x) (hμ : μ < 1) (hr : 0 < r)
    (hroot : μ < p ^ ((r : ℝ)⁻¹))
    (hbound : x < weightedBookParameter p μ θ r) :
    x ^ ((r : ℝ)⁻¹) * (1 - μ) ^ (1 - θ * (r : ℝ)⁻¹) + μ <
      p ^ ((r : ℝ)⁻¹) := by
  let A := p ^ ((r : ℝ)⁻¹) - μ
  let B := 1 - μ
  have hA : 0 < A := sub_pos.mpr hroot
  have hB : 0 < B := sub_pos.mpr hμ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hi : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  rw [weightedBookParameter_eq hμ r] at hbound
  have hpow := Real.rpow_lt_rpow hx.le hbound hi
  have he : (θ - (r : ℝ)) * (r : ℝ)⁻¹ = θ * (r : ℝ)⁻¹ - 1 := by
    field_simp
  have hpow' : x ^ ((r : ℝ)⁻¹) < A * B ^ (θ * (r : ℝ)⁻¹ - 1) := by
    calc
      x ^ ((r : ℝ)⁻¹) < (A ^ r * B ^ (θ - (r : ℝ))) ^ ((r : ℝ)⁻¹) := hpow
      _ = (A ^ r) ^ ((r : ℝ)⁻¹) *
          (B ^ (θ - (r : ℝ))) ^ ((r : ℝ)⁻¹) :=
        Real.mul_rpow (pow_nonneg hA.le _) (Real.rpow_nonneg hB.le _) _
      _ = A * B ^ (θ * (r : ℝ)⁻¹ - 1) := by
        rw [Real.pow_rpow_inv_natCast hA.le hr.ne', ← Real.rpow_mul hB.le, he]
  have hmul := mul_lt_mul_of_pos_right hpow'
    (Real.rpow_pos_of_pos hB (1 - θ * (r : ℝ)⁻¹))
  have hc : B ^ (θ * (r : ℝ)⁻¹ - 1) * B ^ (1 - θ * (r : ℝ)⁻¹) = 1 := by
    rw [← Real.rpow_add hB]
    have : (θ * (r : ℝ)⁻¹ - 1) + (1 - θ * (r : ℝ)⁻¹) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [mul_assoc, hc, mul_one] at hmul
  dsimp [A, B] at hmul
  linarith

end Ramsey3683Bootstrap
