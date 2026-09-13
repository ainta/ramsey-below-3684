import Ramsey3683Bootstrap.GridCell
import Ramsey3683Bootstrap.GridDensity
import Ramsey3683Bootstrap.GridSeed
import RamseyLean.Frontier

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

/-- One cutoff works for every blue target, including targets between grid
knots. The grid constrains the red size only. -/
def GridProfile (N : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ N*m →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
        Real.exp ((N*m : ℕ)*(F ((ℓ : ℝ)/(N*m : ℕ))+ε)) ≤ (#X : ℝ) →
        hasRedClique G X (N*m) ∨ hasBlueClique G X ℓ

theorem UniformRamseyExpBound.gridProfile {F : ℝ → ℝ} (hF : UniformRamseyExpBound F)
    {N : ℕ} (hN : 0 < N) : GridProfile.{u} N F := by
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hF.eventually ε hε)
  filter_upwards [eventually_ge_atTop K] with m hm
  intro ℓ hℓ hℓk V instF instEq G instAdj X hX
  have hbound := hK (N*m) (hm.trans (Nat.le_mul_of_pos_left m hN)) ℓ hℓ hℓk
  have hcard : ramseyNumber (N*m) ℓ ≤ #X := by
    have hX' : Real.exp ((F ((ℓ : ℝ)/(N*m : ℕ))+ε)*(N*m : ℕ)) ≤ (#X : ℝ) := by
      simpa only [mul_comm] using hX
    exact_mod_cast hbound.trans hX'
  exact ((ramseyNumber_spec (N*m) ℓ).mono hcard).on_finset G X rfl

theorem GridProfile.row {N i : ℕ} {F : ℝ → ℝ} (hN : 0 < N)
    (hi : 0 < i) (hiN : i ≤ N) (h : GridProfile.{u} N F) :
    GridUnconditional.{u} N i (F ((i : ℝ)/N)) := by
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop 0] with m hm hm0
  intro V instF instEq G instAdj X hX
  apply hm (i*m) (Nat.mul_pos hi hm0) (Nat.mul_le_mul_right m hiN)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  simpa only [Nat.cast_mul, mul_div_mul_right _ _ hmR] using hX

theorem ramseyNumber_mono_targets {k ℓ k' ℓ' : ℕ} (hk : k ≤ k') (hℓ : ℓ ≤ ℓ') :
    ramseyNumber k ℓ ≤ ramseyNumber k' ℓ' := by
  apply ramseyNumber_le
  intro G
  classical
  rcases ramseyNumber_spec k' ℓ' G with hr | hb
  · exact Or.inl (redClique_lower hk hr)
  · exact Or.inr (blueClique_lower hℓ hb)

theorem GridProfile.ramsey_grid {N : ℕ} {F : ℝ → ℝ} (hN : 0 < N)
    (hF : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r) (h : GridProfile.{0} N F) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ N*m →
      (ramseyNumber (N*m) ℓ : ℝ) ≤ Real.exp ((N*m : ℕ)*(F ((ℓ : ℝ)/(N*m : ℕ))+ε)) := by
  intro ε hε
  have hεhalf : 0 < ε/2 := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  filter_upwards [h (ε/2) hεhalf, eventually_ceil_exp_padding (mul_pos hNr hεhalf)] with m hm hpad
  intro ℓ hℓ hℓk
  have hkr : (0 : ℝ) < (N*m : ℕ) := by exact_mod_cast hℓ.trans_le hℓk
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hr : (ℓ : ℝ)/(N*m : ℕ) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hℓr hkr, (div_le_one hkr).mpr (by exact_mod_cast hℓk)⟩
  let a := (N*m : ℕ)*(F ((ℓ : ℝ)/(N*m : ℕ))+ε/2)
  have hb : RamseyBound (N*m) ℓ (ceilThreshold (Real.exp a)) := by
    intro G
    classical
    apply hm ℓ hℓ hℓk
    simpa only [Finset.card_univ, Fintype.card_fin] using exp_le_ceilThreshold a
  have hR : (ramseyNumber (N*m) ℓ : ℝ) ≤ ceilThreshold (Real.exp a) := by
    exact_mod_cast ramseyNumber_le hb
  apply hR.trans
  have ha : 0 ≤ a := mul_nonneg hkr.le (add_nonneg (hF _ hr) hεhalf.le)
  have he : a + ((N : ℝ)*(ε/2))*m = (N*m : ℕ)*(F ((ℓ : ℝ)/(N*m : ℕ))+ε) := by
    dsimp [a]; push_cast; ring
  simpa only [he] using hpad a ha

/-- Monotonicity removes the red-size grid restriction with only a fixed
additive error in the exponent. No Lipschitz bound or finer mesh is needed. -/
theorem GridProfile.uniform {N : ℕ} {F : ℝ → ℝ} (hN : 0 < N)
    (hF : ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ F r) (hmono : MonotoneOn F (Ioc (0 : ℝ) 1))
    (h : GridProfile.{0} N F) : UniformRamseyExpBound F := by
  apply uniformRamseyExpBound_of_eventually
  intro ε hε
  have hεhalf : 0 < ε/2 := by linarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp (h.ramsey_grid hN hF (ε/2) hεhalf)
  have ht : Tendsto (fun k : ℕ => (ε/2)*(k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hεhalf
  filter_upwards [eventually_ge_atTop (K*N),
    ht.eventually_ge_atTop ((N : ℝ)*(F 1+ε/2))] with k hkK hkSlack
  intro ℓ hℓ hℓk
  let m := k/N+1
  have hKm : K ≤ m := (Nat.le_div_iff_mul_le hN).mpr hkK |>.trans (Nat.le_succ _)
  have hmod := Nat.mod_lt k hN
  have hdiv := Nat.mod_add_div k N
  have hkm : k ≤ N*m := by dsimp [m]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hmk : N*m ≤ k+N := by dsimp [m]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hℓ.trans_le hℓk
  have hmR : (0 : ℝ) < (N*m : ℕ) := by exact_mod_cast (hℓ.trans_le hℓk).trans_le hkm
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hkmR : (k : ℝ) ≤ (N*m : ℕ) := by exact_mod_cast hkm
  have hmkR : (N*m : ℕ) ≤ (k : ℝ)+N := by exact_mod_cast hmk
  have hr : (ℓ : ℝ)/k ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hℓR hkR, (div_le_one hkR).mpr (by exact_mod_cast hℓk)⟩
  have hr' : (ℓ : ℝ)/(N*m : ℕ) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hℓR hmR, (div_le_one hmR).mpr (by exact_mod_cast hℓk.trans hkm)⟩
  have hrate := hmono hr' hr (div_le_div_of_nonneg_left hℓR.le hkR hkmR)
  have hcap := hmono hr (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) hr.2
  have hbound := hK m hKm ℓ hℓ (hℓk.trans hkm)
  have hR : (ramseyNumber k ℓ : ℝ) ≤ ramseyNumber (N*m) ℓ := by
    exact_mod_cast ramseyNumber_mono_targets hkm (le_refl ℓ)
  apply (hR.trans hbound).trans (Real.exp_le_exp.mpr ?_)
  have hrate' := mul_le_mul_of_nonneg_left (add_le_add_right hrate (ε/2)) hmR.le
  have hsize := mul_le_mul_of_nonneg_right hmkR (add_nonneg (hF _ hr) hεhalf.le)
  have hcap' := mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

theorem region_of_strict_support {F : ℝ → ℝ} {a b δ : ℝ}
    (hF : UniformRamseyExpBound F) (hδ : 0 < δ) (ha : δ < a) (hb : δ < b)
    (hab : ∀ r ∈ Ioc (0 : ℝ) 1, F r ≤ (a-δ)+r*(b-δ))
    (hba : ∀ r ∈ Ioc (0 : ℝ) 1, F r ≤ (b-δ)+r*(a-δ)) :
    (Real.exp (-a),Real.exp (-b)) ∈ asymptoticRegionInterior := by
  have hx : Real.exp (-(a-δ)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  have hy : Real.exp (-(b-δ)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  have hreg := mem_asymptoticRegion_of_uniform_bound hx hy hF
    (by simpa only [Real.log_exp, neg_neg, mul_neg, sub_neg_eq_add] using hab)
    (by simpa only [Real.log_exp, neg_neg, mul_neg, sub_neg_eq_add] using hba)
  exact lower_mem_asymptoticRegionInterior hreg (Real.exp_pos _)
    (Real.exp_lt_exp.mpr (by linarith)) (Real.exp_pos _) (Real.exp_lt_exp.mpr (by linarith))

/-- A finite cover closes an entire round. It can use the old profile or
any of the new continuation bands at each ratio. The cover inequalities
are the exact finite piecewise-affine obligations for the certificate. -/
theorem GridProfile.of_cover {N count : ℕ} {P F : ℝ → ℝ}
    (hN : 0 < N) (hP : GridProfile.{u} N P)
    (row : Fin count → ℕ) (start slope : Fin count → ℝ)
    (hbands : ∀ b, GridBand.{u} N (row b) (start b) (slope b))
    (hcover : ∀ r ∈ Ioc (0 : ℝ) 1, P r ≤ F r ∨
      ∃ b : Fin count, (row b : ℝ)/N ≤ r ∧ r ≤ ((row b : ℝ)+1)/N ∧
        start b + slope b*(r-(row b : ℝ)/N) ≤ F r) :
    GridProfile.{u} N F := by
  intro ε hε
  have hall : ∀ᶠ m : ℕ in atTop, ∀ b, ∀ t : ℕ, row b*m ≤ t → t ≤ (row b+1)*m →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
        Real.exp (blockExponent N (row b) m (start b) (slope b) ε t) ≤ (#X : ℝ) →
        hasRedClique G X (N*m) ∨ hasBlueClique G X t :=
    Filter.eventually_all.mpr (fun b => hbands b ε hε)
  filter_upwards [hP ε hε, hall, eventually_gt_atTop 0] with m hmP hmBands hm0
  intro ℓ hℓ hℓk V instF instEq G instAdj X hX
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hkR : (0 : ℝ) < (N*m : ℕ) := by exact_mod_cast Nat.mul_pos hN hm0
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  let r := (ℓ : ℝ)/(N*m : ℕ)
  have hr : r ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos hℓR hkR, (div_le_one hkR).mpr (by exact_mod_cast hℓk)⟩
  rcases hcover r hr with hold | ⟨b,hleft,hright,hline⟩
  · apply hmP ℓ hℓ hℓk
    apply le_trans _ hX
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add hold (le_refl ε)) hkR.le)
  · have hl : row b*m ≤ ℓ := by
      have he : ((row b*m : ℕ) : ℝ)/(N*m : ℕ) = (row b : ℝ)/N := by
        simp only [Nat.cast_mul, mul_div_mul_right _ _ hmR]
      have h := (div_le_div_iff_of_pos_right hkR).mp (he ▸ hleft)
      exact_mod_cast h
    have hu : ℓ ≤ (row b+1)*m := by
      have he : (((row b+1)*m : ℕ) : ℝ)/(N*m : ℕ) = ((row b : ℝ)+1)/N := by
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_div_mul_right _ _ hmR]
      have h := (div_le_div_iff_of_pos_right hkR).mp (he ▸ hright)
      exact_mod_cast h
    apply hmBands b ℓ hl hu
    apply le_trans _ hX
    apply Real.exp_le_exp.mpr
    have he : blockExponent N (row b) m (start b) (slope b) ε ℓ =
        (N*m : ℕ)*(start b+slope b*(r-(row b : ℝ)/N)+ε) := by
      dsimp [blockExponent,r]
      push_cast
      field_simp
      <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (add_le_add hline (le_refl ε)) hkR.le

theorem GridUnconditional.weaken {N i : ℕ} {u v : ℝ} (h : GridUnconditional.{u} N i u)
    (huv : u ≤ v) : GridUnconditional.{u} N i v := by
  intro ε hε
  filter_upwards [h ε hε] with m hm
  intro V instF instEq G instAdj X hX
  apply hm
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add huv (le_refl ε))
    (Nat.cast_nonneg (N*m)))).trans hX

theorem GridCandidate.weaken {N j i : ℕ} {u v u' v' p : ℝ}
    (h : GridCandidate.{u} N j i u v p) (hu : u ≤ u') (hv : v ≤ v') :
    GridCandidate.{u} N j i u' v' p := by
  intro ε hε
  filter_upwards [h ε hε] with m hm
  intro V instF instEq G instAdj X Y hc hr hX hY
  apply hm hc hr
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add hu (le_refl ε))
      (Nat.cast_nonneg (N*m)))).trans hX
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (add_le_add hv (le_refl ε))
      (Nat.cast_nonneg (N*m)))).trans hY

/-- Interpret a whole continuation path. The proof is by induction on its
row interval; certificate compression is free to establish the displayed
pointwise arithmetic premises with shared range summaries. -/
theorem GridCandidate.path {N j lo hi : ℕ} {v p : ℝ}
    (exponent cost floor density : ℕ → ℝ)
    (hN : 0 < N) (hlohi : lo ≤ hi) (hv : 0 < v)
    (hpos : ∀ i, lo ≤ i → i ≤ hi → 0 < exponent i)
    (hcost : ∀ i, lo < i → i ≤ hi → 0 < cost i)
    (hq : ∀ i, lo < i → i ≤ hi → density i < 1)
    (hslope : ∀ i, lo < i → i ≤ hi → 0 < cost i + Real.log (1-density i))
    (hsize : ∀ i, lo < i → i ≤ hi → floor i < exponent (i-1))
    (hstep : ∀ i, lo < i → i ≤ hi → exponent i = exponent (i-1)+cost i/N)
    (hd : ∀ i, lo < i → i ≤ hi → GridDensity.{u} N i (floor i) (density i))
    (hbase : GridCandidate.{u} N j lo (exponent lo) v p) :
    GridCandidate.{u} N j hi (exponent hi) v p := by
  have haux : ∀ i, lo ≤ i → i ≤ hi → GridCandidate.{u} N j i (exponent i) v p := by
    intro i hli
    induction i,hli using Nat.le_induction with
    | base => intro _; exact hbase
    | succ i hli ih =>
      intro hihi
      have hgt : lo < i+1 := by omega
      have hprev : i ≤ hi := by omega
      rw [hstep (i+1) hgt hihi]
      simp only [Nat.add_sub_cancel]
      exact (ih hprev).cell hN (hpos i hli hprev) hv (hcost (i+1) hgt hihi)
        (hq (i+1) hgt hihi) (hslope (i+1) hgt hihi)
        (by simpa only [Nat.add_sub_cancel] using hsize (i+1) hgt hihi)
        (hd (i+1) hgt hihi)
  exact haux hi hlohi le_rfl

theorem GridUnconditional.path {N lo hi : ℕ}
    (exponent cost floor density : ℕ → ℝ)
    (hN : 0 < N) (hlohi : lo ≤ hi)
    (hpos : ∀ i, lo ≤ i → i ≤ hi → 0 < exponent i)
    (hcost : ∀ i, lo < i → i ≤ hi → 0 < cost i)
    (hq : ∀ i, lo < i → i ≤ hi → density i < 1)
    (hslope : ∀ i, lo < i → i ≤ hi → 0 < cost i + Real.log (1-density i))
    (hsize : ∀ i, lo < i → i ≤ hi → floor i < exponent (i-1))
    (hstep : ∀ i, lo < i → i ≤ hi → exponent i = exponent (i-1)+cost i/N)
    (hd : ∀ i, lo < i → i ≤ hi → GridDensity.{u} N i (floor i) (density i))
    (hbase : GridUnconditional.{u} N lo (exponent lo)) :
    GridUnconditional.{u} N hi (exponent hi) ∧
      ∀ i, lo ≤ i → i < hi → GridBand.{u} N i (exponent i) (cost (i+1)) := by
  have haux : ∀ i, lo ≤ i → i ≤ hi → GridUnconditional.{u} N i (exponent i) := by
    intro i hli
    induction i,hli using Nat.le_induction with
    | base => intro _; exact hbase
    | succ i hli ih =>
      intro hihi
      have hgt : lo < i+1 := by omega
      have hprev : i ≤ hi := by omega
      rw [hstep (i+1) hgt hihi]
      simp only [Nat.add_sub_cancel]
      exact ((ih hprev).band hN (hpos i hli hprev) (hcost (i+1) hgt hihi)
        (hq (i+1) hgt hihi) (hslope (i+1) hgt hihi)
        (by simpa only [Nat.add_sub_cancel] using hsize (i+1) hgt hihi)
        (hd (i+1) hgt hihi)).endpoint hN
  refine ⟨haux hi hlohi le_rfl, ?_⟩
  intro i hli hihi
  have hgt : lo < i+1 := by omega
  have hnext : i+1 ≤ hi := by omega
  exact (haux i hli hihi.le).band hN (hpos i hli hihi.le) (hcost (i+1) hgt hnext)
    (hq (i+1) hgt hnext) (hslope (i+1) hgt hnext)
    (by simpa only [Nat.add_sub_cancel] using hsize (i+1) hgt hnext)
    (hd (i+1) hgt hnext)

structure AffineLine where
  intercept : ℝ
  slope : ℝ

def AffineLine.eval (line : AffineLine) (r : ℝ) : ℝ := line.intercept+line.slope*r

noncomputable def affineProfile {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine) (r : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (lines i).eval r)

theorem affineProfile_le {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine) (i : ι) (r : ℝ) :
    affineProfile lines r ≤ (lines i).eval r :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem affineProfile_nonneg {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine)
    (ha : ∀ i, 0 ≤ (lines i).intercept) (hb : ∀ i, 0 ≤ (lines i).slope)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ affineProfile lines r := by
  apply Finset.le_inf'
  intro i _
  exact add_nonneg (ha i) (mul_nonneg (hb i) hr)

theorem affineProfile_monotone {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine)
    (hb : ∀ i, 0 ≤ (lines i).slope) : Monotone (affineProfile lines) := by
  intro r s hrs
  apply Finset.le_inf'
  intro i _
  exact (affineProfile_le lines i r).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrs (hb i)))

/-- Only two existing lines are needed for a supporting-line witness.
There is no scan across all knots for each weighted seed. -/
theorem affineProfile_support {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine)
    (i j : ι) {weight a b : ℝ} (hweight : weight ∈ Icc (0 : ℝ) 1)
    (ha : weight*(lines i).intercept+(1-weight)*(lines j).intercept ≤ a)
    (hb : weight*(lines i).slope+(1-weight)*(lines j).slope ≤ b)
    {r : ℝ} (hr : 0 ≤ r) : affineProfile lines r ≤ a+b*r := by
  have hleft := mul_le_mul_of_nonneg_left (affineProfile_le lines i r) hweight.1
  have hright := mul_le_mul_of_nonneg_left (affineProfile_le lines j r) (sub_nonneg.mpr hweight.2)
  have hslope := mul_le_mul_of_nonneg_right hb hr
  dsimp [AffineLine.eval] at hleft hright
  nlinarith

theorem GridProfile.affine_minimum {N : ℕ} {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine)
    (h : ∀ i, GridProfile.{u} N (lines i).eval) : GridProfile.{u} N (affineProfile lines) := by
  intro ε hε
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ N*m →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
        Real.exp ((N*m : ℕ)*((lines i).eval ((ℓ : ℝ)/(N*m : ℕ))+ε)) ≤ (#X : ℝ) →
        hasRedClique G X (N*m) ∨ hasBlueClique G X ℓ :=
    Filter.eventually_all.mpr (fun i => h i ε hε)
  filter_upwards [hall] with m hm
  intro ℓ hℓ hℓk V instF instEq G instAdj X hX
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i => (lines i).eval ((ℓ : ℝ)/(N*m : ℕ)))
  apply hm i ℓ hℓ hℓk
  simpa only [affineProfile,he] using hX

theorem UniformRamseyExpBound.affine_minimum {ι : Type} [Fintype ι] [Nonempty ι] (lines : ι → AffineLine)
    (h : ∀ i, UniformRamseyExpBound (lines i).eval) : UniformRamseyExpBound (affineProfile lines) := by
  apply uniformRamseyExpBound_of_eventually
  intro ε hε
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i, ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ k →
      (ramseyNumber k ℓ : ℝ) ≤ Real.exp (((lines i).eval ((ℓ : ℝ)/k)+ε)*k) :=
    Filter.eventually_all.mpr (fun i => (h i).eventually ε hε)
  filter_upwards [hall] with k hk
  intro ℓ hℓ hℓk
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => (lines i).eval ((ℓ : ℝ)/k))
  simpa only [affineProfile,he] using hk i ℓ hℓ hℓk

/-- Certify a whole affine majorant from one tangent and two endpoint
inequalities. This reuses upstream concavity for the initial GNNW profile. -/
theorem affine_majorant_of_tangent {F : ℝ → ℝ} {τ d a b : ℝ}
    (hconcave : ConcaveOn ℝ (Ioc (0 : ℝ) 1) F) (hτ : τ ∈ Ioc (0 : ℝ) 1)
    (hderiv : HasDerivAt F d τ)
    (hzero : F τ-τ*d ≤ a) (hone : F τ+(1-τ)*d ≤ a+b) :
    ∀ r ∈ Ioc (0 : ℝ) 1, F r ≤ a+b*r := by
  intro r hr
  have ht := concaveOn_le_tangentLine (D := fun _ => d) hconcave hr hτ hderiv
  have h0 := mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr hr.2)
  have h1 := mul_le_mul_of_nonneg_left hone hr.1.le
  nlinarith

#print axioms GridProfile.uniform
#print axioms GridProfile.of_cover
#print axioms GridCandidate.path
#print axioms affineProfile_support
end Ramsey3683Bootstrap
