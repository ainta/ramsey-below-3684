import Ramsey3683Bootstrap.FinsetCut

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

/-- The one-shot losses are fixed constants, independent of the graph and
the target sizes. They are paid once by asymptotic exponential slack. -/
theorem exists_prepared_cut_constant {p p₀ : ℝ}
    (hp : 0 ≤ p) (hpp : p < p₀) (hp₀ : p₀ < 1) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj] {W : Finset V},
        2 ≤ #W → InternalRedAtLeast G W p₀ →
        ∃ A B : Finset V, A ⊆ W ∧ B ⊆ W ∧ Candidate G A B ∧ RowFloor G A B p ∧
          κ * (#W : ℝ) ≤ (#A : ℝ) ∧ κ * (#W : ℝ) ≤ (#B : ℝ) := by
  let q := (p + p₀) / 2
  let d := (p₀ - q) / 8
  let f := (q - p) / (1 - p)
  have hpq : p < q := by dsimp [q]; linarith
  have hqp : q < p₀ := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq.le
  have hp1 : p < 1 := hpp.trans hp₀
  have hd : 0 < d := div_pos (sub_pos.mpr hqp) (by norm_num)
  have hf : 0 < f := div_pos (sub_pos.mpr hpq) (sub_pos.mpr hp1)
  refine ⟨min 1 f * d, mul_pos (lt_min (by norm_num) hf) hd, ?_⟩
  intro V instF instEq G instAdj W hW hden
  obtain ⟨A, B, hAB, hcan, hcross, hA, hB⟩ :=
    exists_large_dense_cut G hq hqp hW hden
  obtain ⟨A', hsub, hc', hr', hA'⟩ := exists_prepared_candidate hcan hpq hp1 hcross
  have hAW : A ⊆ W := hAB ▸ Finset.subset_union_left
  have hBW : B ⊆ W := hAB ▸ Finset.subset_union_right
  have hdn : 0 ≤ d * (#W : ℝ) := mul_nonneg hd.le (Nat.cast_nonneg _)
  refine ⟨A', B, hsub.trans hAW, hBW, hc', hr', ?_, ?_⟩
  · calc
      min 1 f * d * (#W : ℝ) = min 1 f * (d * (#W : ℝ)) := by ring
      _ ≤ f * (d * (#W : ℝ)) := mul_le_mul_of_nonneg_right (min_le_right _ _) hdn
      _ ≤ f * (#A : ℝ) := mul_le_mul_of_nonneg_left hA hf.le
      _ ≤ (#A' : ℝ) := hA'
  · calc
      min 1 f * d * (#W : ℝ) = min 1 f * (d * (#W : ℝ)) := by ring
      _ ≤ 1 * (d * (#W : ℝ)) := mul_le_mul_of_nonneg_right (min_le_left _ _) hdn
      _ ≤ (#B : ℝ) := by simpa using hB

theorem eventually_const_mul_exp_padding {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ a : ℝ,
      Real.exp a ≤ κ * Real.exp (a + δ * (m : ℝ)) := by
  have ht : Tendsto (fun m : ℕ => κ * Real.exp (δ * (m : ℝ))) atTop atTop :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop 1] with m hm
  intro a
  have h := mul_le_mul_of_nonneg_right hm (Real.exp_pos a).le
  rw [Real.exp_add]
  nlinarith

/-- Turn the completed candidate row into an ordinary density theorem.
The proof uses actual graph cuts and preparation, not a density oracle. -/
theorem GridCandidate.density {N j : ℕ} {u v p p₀ : ℝ}
    (hN : 0 < N) (hv : 0 < v) (huv : u ≤ v)
    (hp : 0 ≤ p) (hpp : p < p₀) (hp₀ : p₀ < 1)
    (hcan : GridCandidate.{u} N j j u v p) : GridDensity.{u} N j v p₀ := by
  intro ε hε
  obtain ⟨κ, hκ, hcut⟩ := exists_prepared_cut_constant.{u} hp hpp hp₀
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεhalf : 0 < ε / 2 := by linarith
  have hδ : 0 < (N : ℝ) * (ε / 2) := mul_pos hNr hεhalf
  have ht : Tendsto (fun m : ℕ => Real.exp (((N : ℝ) * (v + ε)) * m)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos hNr (by linarith)))
  filter_upwards [hcan (ε / 2) hεhalf, eventually_const_mul_exp_padding hκ hδ,
    ht.eventually_ge_atTop 2] with m hmCan hmPad hmLarge
  intro V instF instEq G instAdj W hW hden
  have hlarge : 2 ≤ #W := by
    have h : (2 : ℝ) ≤ #W := by
      apply le_trans _ hW
      simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hmLarge
    exact_mod_cast h
  obtain ⟨A, B, hAW, hBW, hc, hr, hA, hB⟩ := hcut hlarge hden
  have hsize : Real.exp ((N * m : ℕ) * (v + ε / 2)) ≤ κ * (#W : ℝ) := by
    have h := hmPad ((N * m : ℕ) * (v + ε / 2))
    have he : (N * m : ℕ) * (v + ε / 2) + ((N : ℝ) * (ε / 2)) * m =
        (N * m : ℕ) * (v + ε) := by push_cast; ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left hW hκ.le)
  have hX : Real.exp ((N * m : ℕ) * (u + ε / 2)) ≤ (#A : ℝ) := by
    apply le_trans _ (hsize.trans hA)
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (N * m)))
  rcases hmCan hc hr hX (hsize.trans hB) with hred | hblueA | hblueB
  · exact Or.inl (hasRedClique_mono (Finset.union_subset hAW hBW) hred)
  · exact Or.inr (hasBlueClique_mono hAW hblueA)
  · exact Or.inr (hasBlueClique_mono hBW hblueB)

#print axioms GridCandidate.density
end Ramsey3683Bootstrap
