import Ramsey3683Bootstrap.GridSemantics

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

def blockExponent (N i m : ℕ) (u c δ : ℝ) (t : ℕ) : ℝ :=
  (N * m : ℕ) * (u + δ) + c * ((t : ℝ) - (i * m : ℕ))

theorem blockExponent_start (N i m : ℕ) (u c δ : ℝ) :
    blockExponent N i m u c δ (i * m) = (N * m : ℕ) * (u + δ) := by
  simp [blockExponent]

theorem blockExponent_end {N : ℕ} (hN : 0 < N) (i m : ℕ) (u c δ : ℝ) :
    blockExponent N i m u c δ ((i + 1) * m) =
      (N * m : ℕ) * (u + c / N + δ) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [blockExponent, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem blockExponent_step (N i m : ℕ) (u c δ : ℝ) {t : ℕ} (ht : 0 < t) :
    blockExponent N i m u c δ (t - 1) + c = blockExponent N i m u c δ t := by
  simp only [blockExponent, Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
  ring

theorem blockExponent_lower (N i m : ℕ) (u : ℝ) {c δ : ℝ}
    (hc : 0 ≤ c) (hδ : 0 ≤ δ) {t : ℕ} (ht : i * m ≤ t) :
    (N * m : ℕ) * u ≤ blockExponent N i m u c δ t := by
  have htR : (i * m : ℕ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hp := mul_nonneg hc (sub_nonneg.mpr htR)
  have hp' := mul_nonneg (Nat.cast_nonneg (N * m) : (0 : ℝ) ≤ (N * m : ℕ)) hδ
  dsimp [blockExponent]
  nlinarith

/-- One whole grid cell is continued with one earlier density statement.
The number of integer blue steps is arbitrary, but the Lean proof is fixed.
The cell endpoints coincide with integer targets, eliminating junction
rounding and any need for a robust-density premise. -/
theorem GridCandidate.cell {N j i : ℕ} {u v p w q c : ℝ}
    (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hc : 0 < c)
    (hq : q < 1) (hslope : 0 < c + Real.log (1 - q)) (hsize : w < u)
    (hbase : GridCandidate.{u} N j i u v p)
    (hdensity : GridDensity.{u} N (i + 1) w q) :
    GridCandidate.{u} N j (i + 1) (u + c / N) v p := by
  intro ε hε
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεhalf : 0 < ε / 2 := by linarith
  have hεquarter : 0 < ε / 4 := by linarith
  have hw : 0 < (u - w) / 2 := by linarith
  have hpad : 0 < (N : ℝ) * (ε / 2) := mul_pos hNr hεhalf
  have hlower : 0 < (N : ℝ) * u := mul_pos hNr hu
  filter_upwards [hbase (ε / 4) hεquarter, hdensity ((u - w) / 2) hw,
    eventually_threshold_step hq hslope hlower,
    eventually_ceil_exp_padding hpad, eventually_gt_atTop 0] with m hmBase hmDense hmStep hmPad hm
  intro V instF instEq G instAdj X Y hcan hrow hX hY
  let E := blockExponent N i m u c (ε / 2)
  let A : ℕ → ℕ := fun t => ceilThreshold (Real.exp (E t))
  let B := ceilThreshold (Real.exp ((N * m : ℕ) * (v + ε / 2)))
  have hNm : (0 : ℝ) ≤ (N * m : ℕ) := Nat.cast_nonneg _
  have hXthreshold : A ((i + 1) * m) ≤ #X := by
    have hE : E ((i + 1) * m) = (N * m : ℕ) * (u + c / N + ε / 2) :=
      blockExponent_end hN i m u c (ε / 2)
    have hnonneg : 0 ≤ E ((i + 1) * m) := by
      rw [hE]
      positivity
    have h := hmPad (E ((i + 1) * m)) hnonneg
    have heq : E ((i + 1) * m) + ((N : ℝ) * (ε / 2)) * m =
        (N * m : ℕ) * (u + c / N + ε) := by rw [hE]; push_cast; ring
    rw [heq] at h
    exact_mod_cast h.trans hX
  have hYthreshold : B ≤ #Y := by
    have hnonneg : 0 ≤ (N * m : ℕ) * (v + ε / 2) := by positivity
    have h := hmPad ((N * m : ℕ) * (v + ε / 2)) hnonneg
    have heq : (N * m : ℕ) * (v + ε / 2) + ((N : ℝ) * (ε / 2)) * m =
        (N * m : ℕ) * (v + ε) := by push_cast; ring
    rw [heq] at h
    exact_mod_cast h.trans hY
  apply finite_candidate_continuation G (N * m) (j * m) (i * m) ((i + 1) * m) B A
    (fun _ => q) p (fun t => ceilThreshold_pos _) (fun _ _ _ => hq) ?_ ?_ ?_
    ((i + 1) * m) (Nat.mul_le_mul_right m (Nat.le_succ i)) le_rfl
    X Y hcan hrow hXthreshold hYthreshold
  · intro X' Y' hc' hr' hX' hY'
    apply hmBase hc' hr'
    · have hXr : (A (i * m) : ℝ) ≤ #X' := by exact_mod_cast hX'
      apply le_trans _ hXr
      change Real.exp ((N * m : ℕ) * (u + ε / 4)) ≤
        (ceilThreshold (Real.exp (blockExponent N i m u c (ε / 2) (i * m))) : ℝ)
      rw [blockExponent_start]
      apply le_trans (Real.exp_le_exp.mpr (by nlinarith :
        (N * m : ℕ) * (u + ε / 4) ≤ (N * m : ℕ) * (u + ε / 2)))
      exact exp_le_ceilThreshold _
    · have hYr : (B : ℝ) ≤ #Y' := by exact_mod_cast hY'
      apply le_trans _ hYr
      apply le_trans (Real.exp_le_exp.mpr (by nlinarith :
        (N * m : ℕ) * (v + ε / 4) ≤ (N * m : ℕ) * (v + ε / 2)))
      exact exp_le_ceilThreshold _
  · intro t ht0 ht1 X' hX' hd'
    have hEt : (N * m : ℕ) * u ≤ E t :=
      blockExponent_lower N i m u hc.le hεhalf.le ht0.le
    have horder : Real.exp ((N * m : ℕ) * (w + (u - w) / 2)) ≤ (#X' : ℝ) := by
      apply le_trans _ (show (A t : ℝ) ≤ #X' by exact_mod_cast hX')
      apply le_trans (Real.exp_le_exp.mpr (by nlinarith :
        (N * m : ℕ) * (w + (u - w) / 2) ≤ E t))
      exact exp_le_ceilThreshold (E t)
    rcases hmDense horder hd' with hr | hb
    · exact Or.inl hr
    · exact Or.inr (blueClique_lower ht1 hb)
  · intro t ht0 ht1
    apply hmStep (E (t - 1)) (E t)
    · have h := blockExponent_lower N i m u hc.le hεhalf.le (show i * m ≤ t - 1 by omega)
      simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using h
    · exact (blockExponent_step N i m u c (ε / 2) (by omega)).le

theorem finite_unconditional_continuation
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k t₀ t₁ : ℕ) (A : ℕ → ℕ) (q : ℕ → ℝ)
    (hA : ∀ t, 0 < A t)
    (hq : ∀ t, t₀ < t → t ≤ t₁ → q t < 1)
    (hbase : ∀ X : Finset V, A t₀ ≤ #X → hasRedClique G X k ∨ hasBlueClique G X t₀)
    (hstop : ∀ t, t₀ < t → t ≤ t₁ → ∀ X : Finset V,
      A t ≤ #X → InternalRedAtLeast G X (q t) → hasRedClique G X k ∨ hasBlueClique G X t)
    (hstep : ∀ t, t₀ < t → t ≤ t₁ →
      (A (t-1) : ℝ) ≤ (1-q t) * ((A t : ℝ)-1)) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → ∀ X : Finset V,
      A t ≤ #X → hasRedClique G X k ∨ hasBlueClique G X t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht₀ ht₁ X hX
    by_cases he : t = t₀
    · subst t; exact hbase X hX
    have hgt : t₀ < t := by omega
    by_cases hd : InternalRedAtLeast G X (q t)
    · exact hstop t hgt ht₁ X hX hd
    have hne : X.Nonempty := Finset.card_pos.mp ((hA t).trans_le hX)
    obtain ⟨v,hv,hblue⟩ := exists_blue_neighbourhood_of_not_dense G hne hd
    let T := Gᶜ.neighborFinset v ∩ X
    have hXr : (A t : ℝ) ≤ #X := by exact_mod_cast hX
    have hcardR : (A (t-1) : ℝ) ≤ #T := calc
      _ ≤ (1-q t) * ((A t : ℝ)-1) := hstep t hgt ht₁
      _ ≤ (1-q t) * ((#X : ℝ)-1) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr (hq t hgt ht₁).le)
      _ ≤ (#T : ℝ) := hblue.le
    have hcard : A (t-1) ≤ #T := by exact_mod_cast hcardR
    rcases ih (t-1) (by omega) (by omega) (by omega) T hcard with hr | hb
    · exact Or.inl (hasRedClique_mono Finset.inter_subset_right hr)
    · apply Or.inr
      have hext := hasBlueClique_insert_of_subset_neighborFinset hb
        (show T ⊆ Gᶜ.neighborFinset v from Finset.inter_subset_left)
      have hext' := hasBlueClique_mono
        (Finset.insert_subset hv (show T ⊆ X from Finset.inter_subset_right)) hext
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hext'

/-- Uniform statements inside a cell are retained, not just its endpoint.
This prevents a fixed grid-rounding loss in the final affine profile. -/
def GridBand (N i : ℕ) (u c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ t : ℕ, i*m ≤ t → t ≤ (i+1)*m →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
        Real.exp (blockExponent N i m u c ε t) ≤ (#X : ℝ) →
        hasRedClique G X (N*m) ∨ hasBlueClique G X t

theorem GridUnconditional.band {N i : ℕ} {u w q c : ℝ}
    (hN : 0 < N) (hu : 0 < u) (hc : 0 < c)
    (hq : q < 1) (hslope : 0 < c + Real.log (1-q)) (hsize : w < u)
    (hbase : GridUnconditional.{u} N i u) (hdensity : GridDensity.{u} N (i+1) w q) :
    GridBand.{u} N i u c := by
  intro ε hε
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεhalf : 0 < ε/2 := by linarith
  have hεquarter : 0 < ε/4 := by linarith
  have hw : 0 < (u-w)/2 := by linarith
  have hpad : 0 < (N : ℝ)*(ε/2) := mul_pos hNr hεhalf
  filter_upwards [hbase (ε/4) hεquarter, hdensity ((u-w)/2) hw,
    eventually_threshold_step hq hslope (mul_pos hNr hu),
    eventually_ceil_exp_padding hpad] with m hmBase hmDense hmStep hmPad
  intro t ht0 ht1 V instF instEq G instAdj X hX
  let E := blockExponent N i m u c (ε/2)
  let A : ℕ → ℕ := fun t => ceilThreshold (Real.exp (E t))
  have hNm : (0 : ℝ) ≤ (N*m : ℕ) := Nat.cast_nonneg _
  have hthreshold : A t ≤ #X := by
    have hnonneg : 0 ≤ E t := (mul_nonneg hNm hu.le).trans
      (blockExponent_lower N i m u hc.le hεhalf.le ht0)
    have h := hmPad (E t) hnonneg
    have he : E t + ((N : ℝ)*(ε/2))*m = blockExponent N i m u c ε t := by
      dsimp [E,blockExponent]; push_cast; ring
    rw [he] at h
    exact_mod_cast h.trans hX
  apply finite_unconditional_continuation G (N*m) (i*m) ((i+1)*m) A (fun _ => q)
    (fun _ => ceilThreshold_pos _) (fun _ _ _ => hq) ?_ ?_ ?_ t ht0 ht1 X hthreshold
  · intro X' hX'
    apply hmBase
    apply le_trans _ (show (A (i*m) : ℝ) ≤ #X' by exact_mod_cast hX')
    change Real.exp ((N*m : ℕ)*(u+ε/4)) ≤
      (ceilThreshold (Real.exp (blockExponent N i m u c (ε/2) (i*m))) : ℝ)
    rw [blockExponent_start]
    apply le_trans (Real.exp_le_exp.mpr (by nlinarith :
      (N*m : ℕ)*(u+ε/4) ≤ (N*m : ℕ)*(u+ε/2)))
    exact exp_le_ceilThreshold _
  · intro t' ht'0 ht'1 X' hX' hd'
    have hEt : (N*m : ℕ)*u ≤ E t' :=
      blockExponent_lower N i m u hc.le hεhalf.le ht'0.le
    have horder : Real.exp ((N*m : ℕ)*(w+(u-w)/2)) ≤ (#X' : ℝ) := by
      apply le_trans _ (show (A t' : ℝ) ≤ #X' by exact_mod_cast hX')
      apply le_trans (Real.exp_le_exp.mpr (by nlinarith :
        (N*m : ℕ)*(w+(u-w)/2) ≤ E t'))
      exact exp_le_ceilThreshold _
    rcases hmDense horder hd' with hr | hb
    · exact Or.inl hr
    · exact Or.inr (blueClique_lower ht'1 hb)
  · intro t' ht'0 ht'1
    apply hmStep (E (t'-1)) (E t')
    · have h := blockExponent_lower N i m u hc.le hεhalf.le (show i*m ≤ t'-1 by omega)
      simpa only [Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using h
    · exact (blockExponent_step N i m u c (ε/2) (by omega)).le

theorem GridBand.endpoint {N i : ℕ} {u c : ℝ} (hN : 0 < N) (h : GridBand.{u} N i u c) :
    GridUnconditional.{u} N (i+1) (u+c/N) := by
  intro ε hε
  filter_upwards [h ε hε] with m hm
  intro V instF instEq G instAdj X hX
  apply hm ((i+1)*m) (Nat.mul_le_mul_right m (Nat.le_succ i)) le_rfl
  simpa only [blockExponent_end hN] using hX

#print axioms GridUnconditional.band
end Ramsey3683Bootstrap
