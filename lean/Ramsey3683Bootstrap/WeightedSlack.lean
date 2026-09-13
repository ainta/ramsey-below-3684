import Ramsey3683Bootstrap.WeightedSchedules

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology

theorem weighted_limiting_root_lt {x μ p θ : ℝ}
    (hx : 0 < x) (hμ : μ < 1) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ)
    (hbound : x < p ^ (1 / (1 - μ)) * (1 - μ) ^ θ) :
    x ^ θ⁻¹ + μ < 1 := by
  have hb : 0 < 1 - μ := sub_pos.mpr hμ
  have hpp : p ^ (1 / (1 - μ)) < 1 :=
    Real.rpow_lt_one hp.1.le hp.2 (by positivity)
  have hxB : x < (1 - μ) ^ θ := hbound.trans
    (by simpa using mul_lt_mul_of_pos_right hpp (Real.rpow_pos_of_pos hb θ))
  have h := Real.rpow_lt_rpow hx.le hxB (inv_pos.mpr hθ)
  rw [← Real.rpow_mul hb.le, mul_inv_cancel₀ hθ.ne', Real.rpow_one] at h
  linarith

/-- Only strict scalar slack is selected here; no candidate theorem or
certificate correctness is assumed by this structure. -/
structure WeightedSlack (x₀ y₀ μ₀ p θ : ℝ) where
  r : ℕ
  η : ℝ
  r_pos : 0 < r
  θ_lt_r : θ < (r : ℝ)
  η_pos : 0 < η
  two_eta_lt : 2 * η < p
  high_lt_one : μ₀ + 2 * η < 1
  region : (x₀ + 2 * η, y₀ + 2 * η) ∈ asymptoticRegionInterior
  cutoff : μ₀ + 2 * η < (μ₀ + η) / ((x₀ + η) ^ θ⁻¹ + (μ₀ + η))
  critical :
    (x₀ + η) ^ ((r : ℝ)⁻¹) * (1 - (μ₀ + η)) ^ (1 - θ * (r : ℝ)⁻¹) +
      (μ₀ + 2 * η) + η < (p - η) ^ ((r : ℝ)⁻¹)

theorem exists_weightedSlack {x₀ y₀ μ₀ p θ : ℝ}
    (hx : 0 < x₀) (hμ : μ₀ ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hθ : 0 < θ)
    (hbound : x₀ < p ^ (1 / (1 - μ₀)) * (1 - μ₀) ^ θ)
    (hregion : (x₀, y₀) ∈ asymptoticRegionInterior) :
    Nonempty (WeightedSlack x₀ y₀ μ₀ p θ) := by
  obtain ⟨r, hr2, hθr, hroot, hparam⟩ := exists_weightedBookExponent hp.1 hμ.2 hbound
  have hr : 0 < r := by omega
  have hgap := weighted_root_gap hx hμ.2 hr hroot hparam
  have hsum := weighted_limiting_root_lt hx hμ.2 hp hθ hbound
  have hden : 0 < x₀ ^ θ⁻¹ + μ₀ := add_pos (Real.rpow_pos_of_pos hx _) hμ.1
  have hcut : μ₀ < μ₀ / (x₀ ^ θ⁻¹ + μ₀) := by
    rw [lt_div_iff₀ hden]
    exact mul_lt_of_lt_one_right hμ.1 hsum
  have hxp : ContinuousAt (fun e : ℝ => (x₀ + e) ^ ((r : ℝ)⁻¹)) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by simpa using hx.ne'))
  have hbp : ContinuousAt
      (fun e : ℝ => (1 - (μ₀ + e)) ^ (1 - θ * (r : ℝ)⁻¹)) 0 :=
    (continuousAt_const.sub (continuousAt_const.add continuousAt_id)).rpow_const
      (Or.inl (by simpa using (sub_pos.mpr hμ.2).ne'))
  have hpp : ContinuousAt (fun e : ℝ => (p - e) ^ ((r : ℝ)⁻¹)) 0 :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (by simpa using hp.1.ne'))
  have hcritical : ∀ᶠ e : ℝ in 𝓝 0,
      (x₀ + e) ^ ((r : ℝ)⁻¹) * (1 - (μ₀ + e)) ^ (1 - θ * (r : ℝ)⁻¹) +
        (μ₀ + 2 * e) + e < (p - e) ^ ((r : ℝ)⁻¹) := by
    apply (((hxp.mul hbp).add
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id))).add
      continuousAt_id).eventually_lt hpp
    simpa using hgap
  have hcutoff : ∀ᶠ e : ℝ in 𝓝 0,
      μ₀ + 2 * e < (μ₀ + e) / ((x₀ + e) ^ θ⁻¹ + (μ₀ + e)) := by
    have hc : ContinuousAt (fun e : ℝ => (x₀ + e) ^ θ⁻¹ + (μ₀ + e)) 0 :=
      ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by simpa using hx.ne'))).add (continuousAt_const.add continuousAt_id)
    apply (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_lt
      ((continuousAt_const.add continuousAt_id).div hc (by simpa using hden.ne'))
    simpa using hcut
  have hreg : ∀ᶠ e : ℝ in 𝓝 0,
      (x₀ + 2 * e, y₀ + 2 * e) ∈ asymptoticRegionInterior := by
    have hc : ContinuousAt (fun e : ℝ => (x₀ + 2 * e, y₀ + 2 * e)) 0 :=
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).prodMk
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
    exact hc.eventually_mem (isOpen_interior.mem_nhds
      (by simpa [asymptoticRegionInterior] using hregion))
  have hhigh : ∀ᶠ e : ℝ in 𝓝 0, μ₀ + 2 * e < 1 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually
      (Iio_mem_nhds (by simpa using hμ.2))
  have hsmall : ∀ᶠ e : ℝ in 𝓝 0, 2 * e < p :=
    (continuousAt_const.mul continuousAt_id).eventually
      (Iio_mem_nhds (by simpa using hp.1))
  have hall := hsmall.and (hhigh.and (hreg.and (hcutoff.and hcritical)))
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  obtain ⟨η, hη, hηpos⟩ := (mem_closure_iff_nhds.mp hzero) _ hall
  exact ⟨⟨r, η, hr, hθr, hηpos, hη.1, hη.2.1,
    hη.2.2.1, hη.2.2.2.1, hη.2.2.2.2⟩⟩

structure WeightedGrowth (x₀ y₀ μ₀ p θ : ℝ) (s : WeightedSlack x₀ y₀ μ₀ p θ) where
  e : ℝ
  R : ℕ
  e_mem : e ∈ Ioo (0 : ℝ) 1
  e_le_eta : e ≤ s.η
  R_pos : 0 < R
  r_le_R : s.r ≤ R
  r_le_Rtheta : (s.r : ℝ) ≤ (R : ℝ) * θ
  red_growth : (1 + e) ^ θ * (x₀ + s.η) ≤ x₀ + 2 * s.η
  right_growth : (1 + e) ^ θ * (y₀ + s.η) ≤ y₀ + 2 * s.η
  blue_growth : (1 + e) * (μ₀ + s.η) ≤ 1
  blue_ratio : (1 + e) * (μ₀ + s.η) ≤ μ₀ + 2 * s.η
  red_initial : (1 + e) * x₀ ≤ x₀ + s.η
  right_initial : (1 + e) * y₀ ≤ y₀ + s.η
  blue_initial : (1 + e) * μ₀ ^ θ ≤ (μ₀ + s.η) ^ θ

theorem exists_weightedGrowth {x₀ y₀ μ₀ p θ : ℝ}
    (s : WeightedSlack x₀ y₀ μ₀ p θ) (hμ : 0 < μ₀) (hθ : 0 < θ) :
    Nonempty (WeightedGrowth x₀ y₀ μ₀ p θ s) := by
  obtain ⟨R, hR, hrR, hrθ⟩ := exists_weightedScheduleExponent hθ s.r
  have hηdouble : s.η < 2 * s.η := by linarith [s.η_pos]
  have hc : ContinuousAt (fun e : ℝ => (1 + e) ^ θ) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
  have hred : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) ^ θ * (x₀ + s.η) < x₀ + 2 * s.η :=
    (hc.mul continuousAt_const).eventually (Iio_mem_nhds (by simpa using hηdouble))
  have hright : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) ^ θ * (y₀ + s.η) < y₀ + 2 * s.η :=
    (hc.mul continuousAt_const).eventually (Iio_mem_nhds (by simpa using hηdouble))
  have hblue : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * (μ₀ + s.η) < 1 :=
    ((continuousAt_const.add continuousAt_id).mul continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using (show μ₀ + s.η < 1 by linarith [s.high_lt_one, s.η_pos])))
  have hratio : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * (μ₀ + s.η) < μ₀ + 2 * s.η :=
    ((continuousAt_const.add continuousAt_id).mul continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using hηdouble))
  have hri : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * x₀ < x₀ + s.η :=
    ((continuousAt_const.add continuousAt_id).mul continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using s.η_pos))
  have hyi : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * y₀ < y₀ + s.η :=
    ((continuousAt_const.add continuousAt_id).mul continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using s.η_pos))
  have hbi : ∀ᶠ e : ℝ in 𝓝 0, (1 + e) * μ₀ ^ θ < (μ₀ + s.η) ^ θ :=
    ((continuousAt_const.add continuousAt_id).mul continuousAt_const).eventually
      (Iio_mem_nhds (by simpa using (Real.rpow_lt_rpow hμ.le
        (lt_add_of_pos_right μ₀ s.η_pos) hθ)))
  have hsmall : ∀ᶠ e : ℝ in 𝓝 0, e < min 1 s.η :=
    Iio_mem_nhds (lt_min one_pos s.η_pos)
  have hall := hsmall.and (hred.and (hright.and
    (hblue.and (hratio.and (hri.and (hyi.and hbi))))))
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  obtain ⟨e, he, hepos⟩ := (mem_closure_iff_nhds.mp hzero) _ hall
  rcases he with ⟨he, hred, hright, hblue, hratio, hri, hyi, hbi⟩
  exact ⟨⟨e, R, ⟨hepos, he.trans_le (min_le_left _ _)⟩,
    (he.trans_le (min_le_right _ _)).le, hR, hrR, hrθ,
    hred.le, hright.le, hblue.le, hratio.le, hri.le, hyi.le, hbi.le⟩⟩

end Ramsey3683Bootstrap
