import Ramsey3683Bootstrap.WeightedSlack

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology

noncomputable def weightedConcrete {x y μ p θ : ℝ}
    (s : WeightedSlack x y μ p θ) (g : WeightedGrowth x y μ p θ s) (ℓ : ℕ) :
    WeightedData where
  p := p
  x := x + s.η
  y := y + s.η
  μ := (μ + s.η) ^ θ
  weight := θ
  exponent := s.r
  densityFloor := p - s.η
  highBlueRate := μ + 2 * s.η
  rightTarget := ℓ
  q := fun n => p - s.η / (n : ℝ)
  averagingLoss := fun n => s.η / (n : ℝ) ^ 3
  localGap := fun n => s.η / (n : ℝ) ^ 2
  blueBookGap := fun n => s.η / (n : ℝ) ^ 2
  spineSize := bookSpineSize g.e g.R
  pageCliqueSize := fun n => bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)
  minLeftSize := bookMinimumLeftSize g.e ℓ
  rightRamseyScale := fun k => ((x + 2 * s.η)⁻¹) ^ k * ((y + 2 * s.η)⁻¹) ^ ℓ

private theorem density_gain {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 2 ≤ n) :
    η / (n : ℝ) ^ 3 + η / (n : ℝ) ^ 2 ≤
      (η / ((n - 1 : ℕ) : ℝ)) - η / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hm : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hl : η / (n : ℝ) ^ 3 + η / (n : ℝ) ^ 2 =
      η * (1 + (n : ℝ)) / (n : ℝ) ^ 3 := by field_simp
  have hr : η / ((n - 1 : ℕ) : ℝ) - η / (n : ℝ) =
      η / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
    field_simp
    ring
  rw [hl, hr]
  apply (div_le_div_iff₀ (pow_pos hn0 3) (mul_pos hn0 hm)).2
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

private theorem blue_q_gain {η : ℝ} (hη : 0 < η) {n b : ℕ}
    (hn : 0 < n) (hb : 0 < b) (hbn : b < n) :
    η / (n : ℝ) ^ 2 ≤ η / ((n - b : ℕ) : ℝ) - η / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbnR : (b : ℝ) < n := by exact_mod_cast hbn
  have hdiff : (0 : ℝ) < (n : ℝ) - (b : ℝ) := by linarith
  have hrhs : η / ((n - b : ℕ) : ℝ) - η / (n : ℝ) =
      η * (b : ℝ) / ((n : ℝ) * ((n : ℝ) - (b : ℝ))) := by
    rw [Nat.cast_sub hbn.le]
    field_simp
    ring
  rw [hrhs]
  apply (div_le_div_iff₀ (pow_pos hnR 2) (mul_pos hnR hdiff)).2
  have hprod : (0 : ℝ) ≤ (n : ℝ) * ((b : ℝ) - 1) :=
    mul_nonneg hnR.le (by linarith)
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg hη.le hprod]

theorem weighted_floor_margin {e : ℝ} (he : 0 < e) {n ℓ : ℕ}
    (hlarge : (1 + e) / e ≤ (1 + e) ^ ℓ) :
    (1 + e) ^ (n + (ℓ - 1)) ≤ (bookMinimumLeftSize e ℓ n : ℝ) := by
  have hb : 0 < 1 + e := by linarith
  have hℓ : 0 < ℓ := by
    by_contra hf
    have h0 : ℓ = 0 := by omega
    rw [h0, pow_zero, div_le_iff₀ he] at hlarge
    linarith
  have hE : (1 + e) / e ≤ (1 + e) ^ (n + ℓ) := by
    apply hlarge.trans
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hg : (1 + e) ^ (n + ℓ) / (1 + e) ≤ (1 + e) ^ (n + ℓ) - 1 := by
    rw [div_le_iff₀ hb]
    have hmul := (div_le_iff₀ he).mp hE
    nlinarith
  have hf := Nat.lt_floor_add_one ((1 + e) ^ (n + ℓ))
  have hid : (1 + e) ^ (n + (ℓ - 1)) = (1 + e) ^ (n + ℓ) / (1 + e) := by
    rw [eq_div_iff hb.ne', ← pow_succ]
    congr 1
    omega
  rw [hid]
  exact hg.trans (by dsimp [bookMinimumLeftSize]; linarith)

theorem bookTarget_blue_sub {x y μ : ℝ} (hμ : μ ≠ 0) {t b : ℕ}
    (hbt : b ≤ t) (k ℓ : ℕ) :
    bookTarget x y μ ℓ k (t - b) = μ ^ b * bookTarget x y μ ℓ k t := by
  have he : t = (t - b) + b := by omega
  unfold bookTarget
  conv_rhs => rw [he, pow_add]
  have hcan : μ ^ b * (μ⁻¹) ^ b = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hμ, one_pow]
  calc
    _ = (x⁻¹) ^ k * (y⁻¹) ^ ℓ * (μ⁻¹) ^ (t - b) * (μ ^ b * (μ⁻¹) ^ b) := by
      rw [hcan, mul_one]
    _ = _ := by ring

variable {x y μ p θ : ℝ}

theorem weighted_small_high_blue (s : WeightedSlack x y μ p θ)
    (g : WeightedGrowth x y μ p θ s)
    (hfloor : 0 < p - s.η) {L ℓ n k t : ℕ}
    (hs : BookAsymptoticScaleBounds g.e (μ + 2 * s.η) (p - s.η + g.e) g.R L)
    (hL : L ≤ ℓ - 1) (hl : (1 + g.e) / g.e ≤ (1 + g.e) ^ ℓ)
    (hn : n = k + t) (hk : 2 ≤ k) (ht : 2 ≤ t) :
    (ramseyNumber k (bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)) : ℝ) ≤
      (s.η / (n : ℝ) ^ 3) * (p - s.η) * (bookMinimumLeftSize g.e ℓ n : ℝ) := by
  have hn0 : 0 < n := by omega
  have hram := ramseyNumber_le_pow_first (by omega : 0 < k) (hs.page_pos n hn0)
  have hbound : (ramseyNumber k
      (bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)) : ℝ) ≤
      (n : ℝ) ^ (bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)) := by
    exact_mod_cast hram.trans (Nat.pow_le_pow_left (by omega : k ≤ n) _)
  have hex := hs.exceptional_fraction hn0 hL
  have hf := weighted_floor_margin g.e_mem.1 hl (n := n)
  have hcoeff : 0 ≤ g.e * (p - s.η) / (n : ℝ) ^ 3 := by
    have he := g.e_mem.1
    positivity
  have hcoeff' : g.e * (p - s.η) / (n : ℝ) ^ 3 ≤
      s.η * (p - s.η) / (n : ℝ) ^ 3 := by gcongr; exact g.e_le_eta
  calc
    _ ≤ (n : ℝ) ^ (bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)) := hbound
    _ ≤ (g.e * (p - s.η) / (n : ℝ) ^ 3) * (1 + g.e) ^ (n + (ℓ - 1)) := by
      simpa using hex
    _ ≤ (g.e * (p - s.η) / (n : ℝ) ^ 3) * (bookMinimumLeftSize g.e ℓ n : ℝ) :=
      mul_le_mul_of_nonneg_left hf hcoeff
    _ ≤ (s.η * (p - s.η) / (n : ℝ) ^ 3) * (bookMinimumLeftSize g.e ℓ n : ℝ) := by
      gcongr
    _ = _ := by ring

theorem weighted_concrete_local (s : WeightedSlack x y μ p θ)
    (g : WeightedGrowth x y μ p θ s)
    (hx : 0 < x) (hμ : 0 < μ) (hp : p < 1) (hθ : 0 < θ) {L ℓ : ℕ}
    (hs : BookAsymptoticScaleBounds g.e (μ + 2 * s.η) (p - s.η + g.e) g.R L)
    (hL : L ≤ ℓ - 1) (hl : (1 + g.e) / g.e ≤ (1 + g.e) ^ ℓ) :
    ∀ {n : ℕ} {NX NR NB α αR αB : ℝ},
      4 ≤ n → (bookMinimumLeftSize g.e ℓ n : ℝ) ≤ NX → s.η / (n : ℝ) ^ 2 ≤ α →
      0 ≤ NR → 0 ≤ NB → NR + NB ≤ NX → NB ≤ (μ + 2 * s.η) * NX →
      α * NX ≤ αR * NR + αB * NB + 1 →
      (0 ≤ αR ∧ (x + s.η) * α ^ s.r * NX ^ θ ≤
        (p - s.η) * αR ^ s.r * NR ^ θ) ∨
      (0 ≤ αB ∧ (μ + s.η) ^ θ * α ^ s.r * NX ^ θ ≤
        (p - s.η) * αB ^ s.r * NB ^ θ) := by
  intro n NX NR NB α αR αB hn hNX hαgap hNR hNB hcards hblue hmoment
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have he := g.e_mem.1
  have hη := s.η_pos
  have hfloor : 0 < p - s.η := by linarith [s.two_eta_lt]
  have hf := weighted_floor_margin he hl (n := n)
  have hsize : (n : ℝ) ^ 2 ≤ g.e ^ 2 * NX :=
    (hs.alpha_error n (ℓ - 1) (by omega) hL).trans
      (mul_le_mul_of_nonneg_left (hf.trans hNX) (sq_nonneg g.e))
  have hNXpos : 0 < NX := by
    by_contra hf
    have hc := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg g.e) (le_of_not_gt hf)
    linarith
  have hsize' : (n : ℝ) ^ 2 ≤ s.η ^ 2 * NX := hsize.trans (by
    gcongr
    exact g.e_le_eta)
  have hα : 0 < α := (div_pos hη hn2).trans_le hαgap
  have hone : 1 ≤ s.η * (α * NX) := by
    calc
      1 ≤ (s.η / (n : ℝ) ^ 2) * s.η * NX := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hn2]
        nlinarith [hsize']
      _ ≤ α * s.η * NX := by gcongr
      _ = s.η * (α * NX) := by ring
  have hroot : (p - s.η) ^ ((s.r : ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one hfloor.le (by linarith) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have herr : (p - s.η) ^ ((s.r : ℝ)⁻¹) / (α * NX) ≤ s.η :=
    (div_le_iff₀ (mul_pos hα hNXpos)).2 (hroot.trans hone)
  exact weightedLocalDichotomy s.r_pos hθ s.θ_lt_r (add_pos hx hη) (add_pos hμ hη)
    hfloor (by linarith) s.high_lt_one s.cutoff.le s.critical
    hNXpos hα hNR hNB hcards hblue hmoment herr

theorem weightedConcrete_bounds (s : WeightedSlack x y μ p θ)
    (g : WeightedGrowth x y μ p θ s)
    (hx : 0 < x) (hy : 0 < y) (hμ : 0 < μ) (hp : p < 1) (hθ : 0 < θ)
    {L ℓ : ℕ}
    (hs : BookAsymptoticScaleBounds g.e (μ + 2 * s.η) (p - s.η + g.e) g.R L)
    (hL : L ≤ ℓ - 1) (hl : (1 + g.e) / g.e ≤ (1 + g.e) ^ ℓ)
    (hright : ∀ k, 0 < k → (ramseyNumber k ℓ : ℝ) ≤
      ((x + 2 * s.η)⁻¹) ^ k * ((y + 2 * s.η)⁻¹) ^ ℓ) :
    WeightedBounds (weightedConcrete s g ℓ) := by
  have hη := s.η_pos
  have he := g.e_mem.1
  have hxp : 0 < x + s.η := add_pos hx hη
  have hyp : 0 < y + s.η := add_pos hy hη
  have hμp : 0 < μ + s.η := add_pos hμ hη
  have hfloor : 0 < p - s.η := by linarith [s.two_eta_lt]
  have hhigh : 0 < μ + 2 * s.η := by linarith
  have hL' : L ≤ ℓ := hL.trans (Nat.sub_le ℓ 1)
  refine {
    weight_pos := hθ
    weight_le_exponent := s.θ_lt_r.le
    exponent_pos := s.r_pos
    x_pos := hxp
    y_pos := hyp
    μ_pos := Real.rpow_pos_of_pos hμp θ
    densityFloor_pos := hfloor
    highBlueRate_pos := hhigh
    highBlueRate_lt_one := s.high_lt_one
    q_floor := ?_
    q_le_one := ?_
    averagingLoss_nonneg := ?_
    averagingLoss_lt_floor := ?_
    localGap_pos := ?_
    blueBookGap_nonneg := ?_
    local_density_gain := ?_
    spine_pos := ?_
    pageClique_pos := ?_
    blueBook_scale := ?_
    minLeft_blueBook := ?_
    right_ramsey := hright
    left_large := ?_
    small_high_blue := ?_
    blueBook_q_gain := ?_
    blueBook_moment_gain := ?_
    local_dichotomy := ?_
  }
  · intro n hn
    change p - s.η ≤ p - s.η / (n : ℝ)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    rw [sub_le_sub_iff_left, div_le_iff₀ hn0]
    nlinarith
  · intro n hn
    change p - s.η / (n : ℝ) ≤ 1
    have hd : 0 ≤ s.η / (n : ℝ) := by positivity
    linarith
  · intro n
    change 0 ≤ s.η / (n : ℝ) ^ 3
    positivity
  · intro n hn
    change s.η / (n : ℝ) ^ 3 < p - s.η
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀
      (by exact_mod_cast (by omega : 1 ≤ n))
    have hd : s.η / (n : ℝ) ^ 3 ≤ s.η := by
      rw [div_le_iff₀ (pow_pos hn0 _)]
      nlinarith
    linarith [s.two_eta_lt]
  · intro n hn
    change 0 < s.η / (n : ℝ) ^ 2
    exact div_pos hη (pow_pos (by exact_mod_cast (by omega : 0 < n)) _)
  · intro n hn
    change 0 ≤ s.η / (n : ℝ) ^ 2
    positivity
  · intro n hn
    simp only [weightedConcrete]
    convert density_gain hη (by omega : 2 ≤ n) using 1 <;> ring
  · intro n hn
    exact hs.spine_pos n (by omega)
  · intro n hn
    exact hs.page_pos n (by omega)
  · intro n hn
    exact hs.page_scale n
  · intro n hn
    change 5 * (bookPageSize (μ + 2 * s.η) (bookSpineSize g.e g.R n)) ^ 2 ≤
      ⌊(1 + g.e) ^ (n + ℓ)⌋₊
    apply Nat.le_floor
    exact_mod_cast hs.five_page_sq n ℓ (by omega) hL'
  · intro n k t NX NY d hn hk ht hNX hNY hd hd1 hm hY
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hdiv : s.η / (n : ℝ) ≤ s.η := by
      rw [div_le_iff₀ hn0]
      nlinarith
    have hq : 0 < p - s.η / (n : ℝ) := by linarith
    have hα0 : 0 ≤ d - (p - s.η / (n : ℝ)) := sub_nonneg.mpr hd
    have hα1 : d - (p - s.η / (n : ℝ)) ≤ 1 := by linarith
    have hus : (1 + g.e) ^ θ * (μ + s.η) ^ θ ≤ 1 := by
      rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1 + g.e) hμp.le]
      exact Real.rpow_le_one (by positivity) g.blue_growth hθ.le
    exact weighted_left_large he hθ hxp hyp (Real.rpow_pos_of_pos hμp θ)
      (by linarith) (by linarith) g.red_growth g.right_growth hus
      hn hNX hNY hα0 hα1 hm hY
  · intro n k t hn hk ht
    exact weighted_small_high_blue s g hfloor hs hL hl hn hk ht
  · intro n hn hb
    simp only [weightedConcrete]
    convert blue_q_gain hη (by omega : 0 < n) (hs.spine_pos n (by omega)) hb using 1 <;> ring
  · intro n k t hn hk ht hb
    change bookSpineSize g.e g.R n < t at hb
    simp only [weightedConcrete]
    rw [bookTarget_blue_sub (Real.rpow_pos_of_pos hμp θ).ne' hb.le k ℓ]
    apply mul_le_mul_of_nonneg_right
      (weightedSpine_gain g.e_mem g.e_le_eta hμp hhigh hθ g.r_le_Rtheta g.blue_ratio (by omega))
    unfold bookTarget
    positivity
  · exact weighted_concrete_local s g hx hμ hp hθ hs hL hl

end Ramsey3683Bootstrap
