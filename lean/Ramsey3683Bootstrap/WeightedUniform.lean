import Ramsey3683Bootstrap.WeightedConcrete

/-! Uniform weighted book theorem on upstream graph predicates. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

theorem exists_weightedConcrete_bounds {x y μ p θ : ℝ}
    (s : WeightedSlack x y μ p θ) (g : WeightedGrowth x y μ p θ s)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hp : p < 1) (hθ : 0 < θ)
    {L : ℕ}
    (hs : BookAsymptoticScaleBounds g.e (μ + 2 * s.η) (p - s.η + g.e) g.R L) :
    ∃ L₀ : ℕ, ∀ {ℓ : ℕ}, L₀ ≤ ℓ → WeightedBounds (weightedConcrete s g ℓ) := by
  have htend : Tendsto (fun n : ℕ => (1 + g.e) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith [g.e_mem.1])
  obtain ⟨Nfloor, hfloor⟩ := eventually_atTop.1
    ((tendsto_atTop.1 htend) ((1 + g.e) / g.e))
  obtain ⟨_, _, Nright, hright⟩ := asymptoticRegionInterior_subset_asymptoticRegion0 s.region
  refine ⟨max (L + 1) (max Nfloor Nright), ?_⟩
  intro ℓ hℓ
  have hL : L + 1 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hf : Nfloor ≤ ℓ := (le_max_left _ _).trans ((le_max_right _ _).trans hℓ)
  have hr : Nright ≤ ℓ := (le_max_right _ _).trans ((le_max_right _ _).trans hℓ)
  apply weightedConcrete_bounds s g hx hy hμ hp hθ hs (by omega) (hfloor ℓ hf)
  intro k hk
  exact hright k ℓ hk (by omega) (by omega)

private theorem scaled_target {a x y v x' y' v' : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hy : 0 < y) (hv : 0 < v)
    (hx' : 0 < x') (hy' : 0 < y') (hv' : 0 < v')
    (hsx : a * x ≤ x') (hsy : a * y ≤ y') (hsv : a * v ≤ v')
    (k ℓ t : ℕ) :
    a ^ (k + t + ℓ) * bookTarget x' y' v' ℓ k t ≤ bookTarget x y v ℓ k t := by
  have hscaled : ∀ {z z' : ℝ}, 0 < z → 0 < z' → a * z ≤ z' → a * z'⁻¹ ≤ z⁻¹ := by
    intro z z' hz hz' hs
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hz' hz]
    simpa using hs
  have hk := pow_le_pow_left₀ (mul_nonneg ha (inv_nonneg.mpr hx'.le)) (hscaled hx hx' hsx) k
  have hl := pow_le_pow_left₀ (mul_nonneg ha (inv_nonneg.mpr hy'.le)) (hscaled hy hy' hsy) ℓ
  have ht := pow_le_pow_left₀ (mul_nonneg ha (inv_nonneg.mpr hv'.le)) (hscaled hv hv' hsv) t
  unfold bookTarget
  calc
    a ^ (k + t + ℓ) * ((x'⁻¹) ^ k * (y'⁻¹) ^ ℓ * (v'⁻¹) ^ t) =
        (a * x'⁻¹) ^ k * (a * y'⁻¹) ^ ℓ * (a * v'⁻¹) ^ t := by
      simp only [pow_add, mul_pow]
      ring
    _ ≤ (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (v⁻¹) ^ t :=
      mul_le_mul (mul_le_mul hk hl (by positivity) (by positivity)) ht
        (by positivity) (by positivity)

theorem weighted_initial_gain {e η β p : ℝ} {R r L n ℓ : ℕ}
    (he : e ∈ Ioo (0 : ℝ) 1) (heη : e ≤ η) (hrR : r ≤ R)
    (hs : BookAsymptoticScaleBounds e β p R L) (hn : 0 < n) (hL : L ≤ ℓ) :
    1 ≤ (η / (n : ℝ)) ^ r * (1 + e) ^ (n + ℓ) := by
  have he0 := he.1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hefrac0 : 0 ≤ e / (n : ℝ) := by positivity
  have hefrac1 : e / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]
    exact he.2.le.trans hn1
  have hpow : (e / (n : ℝ)) ^ R ≤ (η / (n : ℝ)) ^ r := by
    apply (pow_le_pow_of_le_one hefrac0 hefrac1 hrR).trans
    apply pow_le_pow_left₀ hefrac0
    exact div_le_div_of_nonneg_right heη hn0.le
  exact (hs.initial_moment_gain he0 hn hL).trans
    (mul_le_mul_of_nonneg_right hpow (by positivity))

theorem weighted_initial_admissible {x y μ p θ : ℝ}
    (s : WeightedSlack x y μ p θ) (g : WeightedGrowth x y μ p θ s)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ)
    {L : ℕ}
    (hs : BookAsymptoticScaleBounds g.e (μ + 2 * s.η) (p - s.η + g.e) g.R L)
    {W : Type u} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {A B : Finset W} {k ℓ t : ℕ} (hk : 0 < k) (ht : 0 < t) (hL : L ≤ ℓ)
    (hc : Candidate H A B) (hd : p ≤ redDensity H A B)
    (hcard : bookTarget x y (μ ^ θ) ℓ k t ≤ (#A : ℝ) ^ θ * (#B : ℝ)) :
    WeightedAdmissible (weightedConcrete s g ℓ) k t H A B := by
  have he := g.e_mem.1
  have hη := s.η_pos
  have hx' := add_pos hx hη
  have hy' := add_pos hy hη
  have hμ' := add_pos hμ hη
  have hn : 0 < k + t := by omega
  have hnR : (0 : ℝ) < (k + t : ℕ) := by exact_mod_cast hn
  have hδ : 0 ≤ s.η / ((k + t : ℕ) : ℝ) := by positivity
  have hq : p - s.η / ((k + t : ℕ) : ℝ) ≤ redDensity H A B := by linarith
  have hbase : s.η / ((k + t : ℕ) : ℝ) ≤
      redDensity H A B - (p - s.η / ((k + t : ℕ) : ℝ)) := by linarith
  have hsc := scaled_target (by positivity : (0 : ℝ) ≤ 1 + g.e) hx hy
    (Real.rpow_pos_of_pos hμ θ) hx' hy' (Real.rpow_pos_of_pos hμ' θ)
    g.red_initial g.right_initial g.blue_initial k ℓ t
  have hgain := weighted_initial_gain g.e_mem g.e_le_eta g.r_le_R hs hn hL
  have htarget0 : 0 ≤ bookTarget (x + s.η) (y + s.η) ((μ + s.η) ^ θ) ℓ k t := by
    unfold bookTarget
    positivity
  refine ⟨hc, hq, ?_⟩
  change bookTarget (x + s.η) (y + s.η) ((μ + s.η) ^ θ) ℓ k t ≤
    (redDensity H A B - (p - s.η / ((k + t : ℕ) : ℝ))) ^ s.r * (#A : ℝ) ^ θ * (#B : ℝ)
  calc
    _ ≤ ((s.η / ((k + t : ℕ) : ℝ)) ^ s.r * (1 + g.e) ^ (k + t + ℓ)) *
        bookTarget (x + s.η) (y + s.η) ((μ + s.η) ^ θ) ℓ k t := by
      simpa using mul_le_mul_of_nonneg_right hgain htarget0
    _ = (s.η / ((k + t : ℕ) : ℝ)) ^ s.r *
        ((1 + g.e) ^ (k + t + ℓ) * bookTarget (x + s.η) (y + s.η) ((μ + s.η) ^ θ) ℓ k t) := by ring
    _ ≤ (s.η / ((k + t : ℕ) : ℝ)) ^ s.r * ((#A : ℝ) ^ θ * (#B : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsc.trans hcard) (pow_nonneg hδ _)
    _ ≤ (redDensity H A B - (p - s.η / ((k + t : ℕ) : ℝ))) ^ s.r *
        ((#A : ℝ) ^ θ * (#B : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hδ hbase s.r) (by positivity)
    _ = _ := by ring

/-- The manuscript's weighted book theorem, uniformly over all left targets,
all finite graphs, and all sufficiently large right targets. There is no
schedule oracle in this statement. -/
theorem isGood_of_density_weighted_card_product {x y μ p θ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hμ : μ ∈ Ioo (0 : ℝ) 1)
    (hp : p ∈ Ioo (0 : ℝ) 1) (hθ : 0 < θ)
    (hbound : x < p ^ (1 / (1 - μ)) * (1 - μ) ^ θ)
    (hregion : (x, y) ∈ asymptoticRegionInterior) :
    ∃ L₀ : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      {H : SimpleGraph W} [DecidableRel H.Adj] {A B : Finset W} {k ℓ t : ℕ},
      0 < k → 0 < ℓ → 0 < t → L₀ ≤ ℓ →
      Candidate H A B → p ≤ redDensity H A B →
      (x⁻¹) ^ k * (y⁻¹) ^ ℓ * ((μ ^ θ)⁻¹) ^ t ≤ (#A : ℝ) ^ θ * (#B : ℝ) →
      Candidate.IsGood H A B k ℓ t := by
  classical
  let s := Classical.choice (exists_weightedSlack hx hμ hp hθ hbound hregion)
  let g := Classical.choice (exists_weightedGrowth s hμ.1 hθ)
  have hhigh : 0 < μ + 2 * s.η := by linarith [hμ.1, s.η_pos]
  have hpe : g.e < p - s.η + g.e := by linarith [s.two_eta_lt, s.η_pos]
  obtain ⟨Lscale, hs⟩ := exists_bookAsymptoticScaleBounds g.e_mem hhigh hpe g.R_pos
  obtain ⟨Lbounds, hb⟩ := exists_weightedConcrete_bounds s g hx hy hμ.1 hp.2 hθ hs
  refine ⟨max Lscale Lbounds, ?_⟩
  intro W instF instEq H instAdj A B k ℓ t hk hℓ ht hL hc hd hcard
  have ha := weighted_initial_admissible s g hx hy hμ.1 hs hk ht
    ((le_max_left _ _).trans hL) hc hd hcard
  exact weightedCandidate_of_bounds (hb ((le_max_right _ _).trans hL)) hk ht ha

#print axioms isGood_of_density_weighted_card_product

end Ramsey3683Bootstrap
