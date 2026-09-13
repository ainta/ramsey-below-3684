import Ramsey3683Bootstrap.WeightedMoment
import Ramsey3683Bootstrap.WeightedLocal

/-!
Finite weighted candidate theorem over actual RamseyLean graphs.

This module separates graph induction from graph-independent numerical
schedules. `weightedCandidate_of_bounds` proves goodness from explicit real
inequalities and actual right-side Ramsey bounds. Constructing these schedules
uniformly from the asymptotic parameter hypotheses is a separate obligation;
this file does not package that missing obligation as a theorem.

`s.μ` is the per-blue-step multiplier in the target. For a manuscript control
mu and weight theta it is mu^theta, not mu.
-/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u

structure WeightedData extends BookInductionData where
  weight : ℝ

structure WeightedBounds (s : WeightedData) : Prop where
  weight_pos : 0 < s.weight
  weight_le_exponent : s.weight ≤ (s.exponent : ℝ)
  exponent_pos : 0 < s.exponent
  x_pos : 0 < s.x
  y_pos : 0 < s.y
  μ_pos : 0 < s.μ
  densityFloor_pos : 0 < s.densityFloor
  highBlueRate_pos : 0 < s.highBlueRate
  highBlueRate_lt_one : s.highBlueRate < 1
  q_floor : ∀ n, 2 ≤ n → s.densityFloor ≤ s.q n
  q_le_one : ∀ n, 2 ≤ n → s.q n ≤ 1
  averagingLoss_nonneg : ∀ n, 0 ≤ s.averagingLoss n
  averagingLoss_lt_floor : ∀ n, 4 ≤ n → s.averagingLoss n < s.densityFloor
  localGap_pos : ∀ n, 4 ≤ n → 0 < s.localGap n
  blueBookGap_nonneg : ∀ n, 4 ≤ n → 0 ≤ s.blueBookGap n
  local_density_gain : ∀ n, 4 ≤ n →
    s.averagingLoss n + s.localGap n ≤ s.q n - s.q (n - 1)
  spine_pos : ∀ n, 4 ≤ n → 0 < s.spineSize n
  pageClique_pos : ∀ n, 4 ≤ n → 0 < s.pageCliqueSize n
  blueBook_scale : ∀ n, 4 ≤ n →
    10 * (s.spineSize n : ℝ) ^ 2 ≤ s.highBlueRate * (s.pageCliqueSize n : ℝ)
  minLeft_blueBook : ∀ n, 4 ≤ n → 5 * (s.pageCliqueSize n) ^ 2 ≤ s.minLeftSize n
  right_ramsey : ∀ k, 0 < k →
    (ramseyNumber k s.rightTarget : ℝ) ≤ s.rightRamseyScale k
  left_large : ∀ {n k t : ℕ} {NX NY d : ℝ},
    n = k + t → 2 ≤ k → 2 ≤ t → 0 < NX → 0 < NY →
    s.q n ≤ d → d ≤ 1 →
    bookTarget s.x s.y s.μ s.rightTarget k t ≤
      (d - s.q n) ^ s.exponent * NX ^ s.weight * NY →
    NY < s.rightRamseyScale k → (s.minLeftSize n : ℝ) ≤ NX
  small_high_blue : ∀ {n k t : ℕ}, n = k + t → 2 ≤ k → 2 ≤ t →
    (ramseyNumber k (s.pageCliqueSize n) : ℝ) ≤
      s.averagingLoss n * s.densityFloor * (s.minLeftSize n : ℝ)
  blueBook_q_gain : ∀ n, 4 ≤ n → s.spineSize n < n →
    s.blueBookGap n ≤ s.q n - s.q (n - s.spineSize n)
  blueBook_moment_gain : ∀ {n k t : ℕ},
    n = k + t → 2 ≤ k → 2 ≤ t → s.spineSize n < t →
    bookTarget s.x s.y s.μ s.rightTarget k (t - s.spineSize n) ≤
      (s.blueBookGap n) ^ s.exponent *
        (s.highBlueRate ^ s.spineSize n / 2) ^ s.weight *
          bookTarget s.x s.y s.μ s.rightTarget k t
  local_dichotomy : ∀ {n : ℕ} {NX NR NB α αR αB : ℝ},
    4 ≤ n → (s.minLeftSize n : ℝ) ≤ NX → s.localGap n ≤ α →
    0 ≤ NR → 0 ≤ NB → NR + NB ≤ NX → NB ≤ s.highBlueRate * NX →
    α * NX ≤ αR * NR + αB * NB + 1 →
    (0 ≤ αR ∧ s.x * α ^ s.exponent * NX ^ s.weight ≤
      s.densityFloor * αR ^ s.exponent * NR ^ s.weight) ∨
    (0 ≤ αB ∧ s.μ * α ^ s.exponent * NX ^ s.weight ≤
      s.densityFloor * αB ^ s.exponent * NB ^ s.weight)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def WeightedAdmissible (s : WeightedData) (k t : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Prop :=
  Candidate G X Y ∧ s.q (k + t) ≤ redDensity G X Y ∧
    bookTarget s.x s.y s.μ s.rightTarget k t ≤
      weightedMoment (s.q (k + t)) s.weight s.exponent G X Y

noncomputable def WeightedStep (s : WeightedData) (k t : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) : Prop :=
  Candidate.IsGood G X Y k s.rightTarget t ∨
    ∃ k' t' : ℕ, ∃ X' Y' : Finset V,
      0 < k' ∧ 0 < t' ∧ k' + t' < k + t ∧
      WeightedAdmissible s k' t' G X' Y' ∧
      (Candidate.IsGood G X' Y' k' s.rightTarget t' →
        Candidate.IsGood G X Y k s.rightTarget t)

theorem weightedStrongInduction {s : WeightedData}
    (hstep : ∀ {k t : ℕ} {X Y : Finset V},
      2 ≤ k → 2 ≤ t → WeightedAdmissible s k t G X Y → WeightedStep s k t G X Y) :
    ∀ {k t : ℕ} {X Y : Finset V}, 0 < k → 0 < t →
      WeightedAdmissible s k t G X Y → Candidate.IsGood G X Y k s.rightTarget t := by
  intro k t X Y hk ht hadm
  induction heq : k + t using Nat.strong_induction_on generalizing k t X Y with
  | h n ih =>
      by_cases hk1 : k = 1
      · subst k
        exact hadm.1.isGood_one_red s.rightTarget t
      by_cases ht1 : t = 1
      · subst t
        exact hadm.1.isGood_one_blue_left k s.rightTarget
      have hk2 : 2 ≤ k := by omega
      have ht2 : 2 ≤ t := by omega
      rcases hstep hk2 ht2 hadm with hg | ⟨k', t', X', Y', hk', ht', hlt, ha, hlift⟩
      · exact hg
      · exact hlift (ih (k' + t') (by omega) (k := k') (t := t')
          (X := X') (Y := Y') hk' ht' ha rfl)

theorem WeightedStep.mono_left {s : WeightedData} {k t : ℕ}
    {X₀ X Y : Finset V} (hX : X₀ ⊆ X) (h : WeightedStep s k t G X₀ Y) :
    WeightedStep s k t G X Y := by
  rcases h with hg | ⟨k', t', X', Y', hk', ht', hlt, hc, hl⟩
  · exact Or.inl (hg.mono hX Finset.Subset.rfl)
  · exact Or.inr ⟨k', t', X', Y', hk', ht', hlt, hc,
      fun hg => (hl hg).mono hX Finset.Subset.rfl⟩

private theorem weightedStep_largeRight {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 0 < k)
    (hY : s.rightRamseyScale k ≤ (#Y : ℝ)) : WeightedStep s k t G X Y := by
  left
  apply Candidate.IsGood.of_ramseyNumber_le_card_right
  exact_mod_cast (hs.right_ramsey k hk).trans hY

private theorem weighted_minLeft {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (ha : WeightedAdmissible s k t G X Y) (hY : (#Y : ℝ) < s.rightRamseyScale k) :
    s.minLeftSize (k + t) ≤ #X := by
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast ha.1.left_card_pos
  have hYpos : (0 : ℝ) < #Y := by exact_mod_cast ha.1.right_card_pos
  have h := hs.left_large rfl hk ht hXpos hYpos ha.2.1
    (redDensity_le_one (G := G) X Y) (by simpa [weightedMoment] using ha.2.2) hY
  exact_mod_cast h

private theorem weighted_regularize {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (ha : WeightedAdmissible s k t G X Y) :
    ∃ X₀ : Finset V, X₀ ⊆ X ∧
      (∀ ⦃C : Finset V⦄, C.Nonempty → C ⊆ X₀ → s.q (k + t) ≤ redDensity G C Y) ∧
      WeightedAdmissible s k t G X₀ Y := by
  obtain ⟨X₀, hsub, hcan, hher, hm⟩ :=
    exists_weightedRegularized ha.1 ha.2.1 hs.weight_le_exponent
  refine ⟨X₀, hsub, hher, hcan, hher hcan.left_nonempty Finset.Subset.rfl, ?_⟩
  exact ha.2.2.trans hm

private theorem weightedStep_manyHighBlue {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (ha : WeightedAdmissible s k t G X Y)
    (hher : ∀ ⦃C : Finset V⦄, C.Nonempty → C ⊆ X → s.q (k + t) ≤ redDensity G C Y)
    (hlarge : s.minLeftSize (k + t) ≤ #X)
    (hmany : ramseyNumber k (s.pageCliqueSize (k + t)) ≤
      #(highBlueVertices G X s.highBlueRate)) : WeightedStep s k t G X Y := by
  classical
  let n := k + t
  let b := s.spineSize n
  let m := s.pageCliqueSize n
  have hn : 4 ≤ n := by omega
  have hb : 0 < b := hs.spine_pos n hn
  have hm : 0 < m := hs.pageClique_pos n hn
  have hXcard : 5 * m ^ 2 ≤ #X := (hs.minLeft_blueBook n hn).trans hlarge
  rcases exists_redClique_or_blueBook hs.highBlueRate_pos hs.highBlueRate_lt_one
      hb (by omega) hm (hs.blueBook_scale n hn) hXcard hmany with
    hred | ⟨S, T, hbook, hST, hS, hTsize⟩
  · exact Or.inl (Candidate.IsGood.of_red
      (hasRedClique_mono Finset.subset_union_left hred))
  · by_cases htb : t ≤ b
    · left
      apply Candidate.IsGood.of_blue_left
      apply hasBlueClique_mono (Finset.subset_union_left.trans hST)
      apply hbook.hasBlueClique_spine_of_le
      simpa [hS] using htb
    have hbt : b < t := Nat.lt_of_not_ge htb
    have hTX : T ⊆ X := Finset.subset_union_right.trans hST
    have hXpos : (0 : ℝ) < #X := by exact_mod_cast ha.1.left_card_pos
    have hratepow : 0 < s.highBlueRate ^ b := pow_pos hs.highBlueRate_pos b
    have hcpos : 0 < s.highBlueRate ^ b / 2 := div_pos hratepow (by norm_num)
    have hTpos : (0 : ℝ) < #T := by
      apply lt_of_lt_of_le _ hTsize
      positivity
    have hT : T.Nonempty := by
      rw [← Finset.card_pos]
      exact_mod_cast hTpos
    have hTC := ha.1.subcandidate hTX Finset.Subset.rfl hT ha.1.right_nonempty
    have hgap : 0 ≤ s.blueBookGap n := hs.blueBookGap_nonneg n hn
    have hqg := hs.blueBook_q_gain n hn (by omega)
    have hqd : s.q (n - b) ≤ redDensity G T Y := by
      linarith [hher hT hTX]
    have hbaseg : s.blueBookGap n ≤ redDensity G T Y - s.q (n - b) := by
      linarith [hher hT hTX]
    have hchild0 : 0 ≤ redDensity G T Y - s.q (n - b) := sub_nonneg.mpr hqd
    have hp0 : 0 ≤ redDensity G X Y - s.q n := sub_nonneg.mpr ha.2.1
    have hq0 : 0 ≤ s.q n := hs.densityFloor_pos.le.trans (hs.q_floor n (by omega))
    have hp1 : redDensity G X Y - s.q n ≤ 1 := by
      linarith [redDensity_le_one (G := G) X Y]
    have hpp : (redDensity G X Y - s.q n) ^ s.exponent ≤ 1 := by
      simpa using pow_le_pow_left₀ hp0 hp1 s.exponent
    have htarget : bookTarget s.x s.y s.μ s.rightTarget k t ≤ (#X : ℝ) ^ s.weight * (#Y : ℝ) := by
      apply ha.2.2.trans
      unfold weightedMoment
      calc
        (redDensity G X Y - s.q (k + t)) ^ s.exponent * (#X : ℝ) ^ s.weight * (#Y : ℝ) ≤
            1 * (#X : ℝ) ^ s.weight * (#Y : ℝ) := by gcongr
        _ = (#X : ℝ) ^ s.weight * (#Y : ℝ) := by ring
    have hTpow : (s.highBlueRate ^ b / 2) ^ s.weight * (#X : ℝ) ^ s.weight ≤
        (#T : ℝ) ^ s.weight := by
      rw [← Real.mul_rpow hcpos.le hXpos.le]
      apply Real.rpow_le_rpow (mul_nonneg hcpos.le hXpos.le) _ hs.weight_pos.le
      convert hTsize using 1 <;> ring
    have hpow := pow_le_pow_left₀ hgap hbaseg s.exponent
    have htarget' : bookTarget s.x s.y s.μ s.rightTarget k (t - b) ≤
        weightedMoment (s.q (k + (t - b))) s.weight s.exponent G T Y := by
      have hnchild : k + (t - b) = n - b := by omega
      rw [hnchild]
      calc
        bookTarget s.x s.y s.μ s.rightTarget k (t - b) ≤
            (s.blueBookGap n) ^ s.exponent * (s.highBlueRate ^ b / 2) ^ s.weight *
              bookTarget s.x s.y s.μ s.rightTarget k t :=
          hs.blueBook_moment_gain rfl hk ht hbt
        _ ≤ (s.blueBookGap n) ^ s.exponent * (s.highBlueRate ^ b / 2) ^ s.weight *
              ((#X : ℝ) ^ s.weight * (#Y : ℝ)) := by
          exact mul_le_mul_of_nonneg_left htarget
            (mul_nonneg (pow_nonneg hgap _) (Real.rpow_nonneg hcpos.le _))
        _ = (s.blueBookGap n) ^ s.exponent *
              ((s.highBlueRate ^ b / 2) ^ s.weight * (#X : ℝ) ^ s.weight) * (#Y : ℝ) := by ring
        _ ≤ (redDensity G T Y - s.q (n - b)) ^ s.exponent * (#T : ℝ) ^ s.weight * (#Y : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hpow hTpow
              (mul_nonneg (Real.rpow_nonneg hcpos.le _) (Real.rpow_nonneg hXpos.le _))
              (pow_nonneg hchild0 _)) (Nat.cast_nonneg #Y)
        _ = weightedMoment (s.q (n - b)) s.weight s.exponent G T Y := rfl
    right
    refine ⟨k, t - b, T, Y, by omega, by omega, by omega, ?_, ?_⟩
    · refine ⟨hTC, ?_, htarget'⟩
      convert hqd using 1 <;> congr 1 <;> omega
    · intro hg
      exact Candidate.IsGood.of_blueBook_extension hbook hg hST hS hbt.le

private theorem weightedStep_fewHighBlue {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (ha : WeightedAdmissible s k t G X Y)
    (hher : ∀ ⦃C : Finset V⦄, C.Nonempty → C ⊆ X → s.q (k + t) ≤ redDensity G C Y)
    (hlarge : s.minLeftSize (k + t) ≤ #X)
    (hfew : #(highBlueVertices G X s.highBlueRate) <
      ramseyNumber k (s.pageCliqueSize (k + t))) : WeightedStep s k t G X Y := by
  classical
  let n := k + t
  let W := highBlueVertices G X s.highBlueRate
  have hn : 4 ≤ n := by omega
  have hWsub : W ⊆ X := highBlueVertices_subset s.highBlueRate
  have hloss0 := hs.averagingLoss_nonneg n
  have hWcard : (#W : ℝ) ≤ s.averagingLoss n * s.densityFloor * (#X : ℝ) := by
    have hw : (#W : ℝ) ≤ (ramseyNumber k (s.pageCliqueSize n) : ℝ) := by
      exact_mod_cast hfew.le
    calc
      (#W : ℝ) ≤ (ramseyNumber k (s.pageCliqueSize n) : ℝ) := hw
      _ ≤ s.averagingLoss n * s.densityFloor * (s.minLeftSize n : ℝ) :=
        hs.small_high_blue rfl hk ht
      _ ≤ s.averagingLoss n * s.densityFloor * (#X : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlarge)
          (mul_nonneg hloss0 hs.densityFloor_pos.le)
  have hρd : s.densityFloor ≤ redDensity G X Y :=
    (hs.q_floor n (by omega)).trans ha.2.1
  obtain ⟨v, hv, hvW, hYne, hsel⟩ := exists_vertex_restrictedDensity_ge
    ha.1 hWsub hs.densityFloor_pos hloss0 (hs.averagingLoss_lt_floor n hn) hρd hWcard
  let Y' := G.neighborFinset v ∩ Y
  let R := G.neighborFinset v ∩ X
  let B := Gᶜ.neighborFinset v ∩ X
  let α := redDensity G X Y' - s.q (n - 1)
  let αR := redDensity G R Y' - s.q (n - 1)
  let αB := redDensity G B Y' - s.q (n - 1)
  have hqgain := hs.local_density_gain n hn
  have hαgap : s.localGap n ≤ α := by
    dsimp [α, Y']
    linarith [ha.2.1]
  have hα : 0 < α := (hs.localGap_pos n hn).trans_le hαgap
  have hselected : redDensity G X Y - s.q n ≤ α := by
    dsimp [α, Y']
    linarith [hs.localGap_pos n hn]
  have hNR : (0 : ℝ) ≤ #R := Nat.cast_nonneg _
  have hNB : (0 : ℝ) ≤ #B := Nat.cast_nonneg _
  have hcards : (#R : ℝ) + (#B : ℝ) ≤ (#X : ℝ) := by
    exact_mod_cast card_red_blue_neighbors_le (G := G) (X := X) (v := v)
  have hblue : (#B : ℝ) ≤ s.highBlueRate * (#X : ℝ) := by
    exact (blueDegree_lt_of_mem_sdiff_highBlueVertices
      (G := G) (X := X) (μ := s.highBlueRate) (Finset.mem_sdiff.mpr ⟨hv, hvW⟩)).le
  have hqchild0 : 0 ≤ s.q (n - 1) :=
    hs.densityFloor_pos.le.trans (hs.q_floor (n - 1) (by omega))
  have hmoment : α * (#X : ℝ) ≤ αR * (#R : ℝ) + αB * (#B : ℝ) + 1 :=
    density_split_red_blue hqchild0 hv (show Y' ⊆ G.neighborFinset v from Finset.inter_subset_left)
  have hright : s.densityFloor * (#Y : ℝ) ≤ (#Y' : ℝ) := by
    have hrow := card_redNeighborhood_ge_of_hereditary hher hv
    exact (mul_le_mul_of_nonneg_right (hs.q_floor n (by omega)) (Nat.cast_nonneg #Y)).trans hrow
  have hNX : (s.minLeftSize n : ℝ) ≤ (#X : ℝ) := by exact_mod_cast hlarge
  have hXpos : (0 : ℝ) < #X := by exact_mod_cast ha.1.left_card_pos
  have hparent0 : 0 ≤ redDensity G X Y - s.q n := sub_nonneg.mpr ha.2.1
  rcases hs.local_dichotomy hn hNX hαgap hNR hNB hcards hblue hmoment with hred | hblue'
  · have hRne : R.Nonempty := by
      by_contra he
      have hR0 := Finset.not_nonempty_iff_eq_empty.mp he
      have hpos : 0 < s.x * α ^ s.exponent * (#X : ℝ) ^ s.weight := by
        exact mul_pos (mul_pos hs.x_pos (pow_pos hα _)) (Real.rpow_pos_of_pos hXpos _)
      have hbad := hred.2
      rw [hR0, Finset.card_empty, Nat.cast_zero, Real.zero_rpow hs.weight_pos.ne', mul_zero] at hbad
      exact (not_le_of_gt hpos) hbad
    have hRC : Candidate G R Y' := ha.1.subcandidate
      Finset.inter_subset_right Finset.inter_subset_right hRne hYne
    have hgain := weightedMoment_child_ge hs.x_pos.le hparent0 hselected hred.1 hred.2 hright
    have hindex : (k - 1) + t = n - 1 := by omega
    have hchild : WeightedAdmissible s (k - 1) t G R Y' := by
      refine ⟨hRC, ?_, ?_⟩
      · rw [hindex]
        exact sub_nonneg.mp hred.1
      · rw [bookTarget_red_pred hs.x_pos.ne' (by omega), hindex]
        exact (mul_le_mul_of_nonneg_left ha.2.2 hs.x_pos.le).trans hgain
    right
    refine ⟨k - 1, t, R, Y', by omega, by omega, by omega, hchild, ?_⟩
    intro hg
    have hl := Candidate.IsGood.of_red_extension hg
      (redNeighborhoodChild_neighbor_subset (G := G) (X := X) (Y := Y) (v := v))
      Finset.inter_subset_right Finset.inter_subset_right hv
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hl
  · have hBne : B.Nonempty := by
      by_contra he
      have hB0 := Finset.not_nonempty_iff_eq_empty.mp he
      have hpos : 0 < s.μ * α ^ s.exponent * (#X : ℝ) ^ s.weight := by
        exact mul_pos (mul_pos hs.μ_pos (pow_pos hα _)) (Real.rpow_pos_of_pos hXpos _)
      have hbad := hblue'.2
      rw [hB0, Finset.card_empty, Nat.cast_zero, Real.zero_rpow hs.weight_pos.ne', mul_zero] at hbad
      exact (not_le_of_gt hpos) hbad
    have hBC : Candidate G B Y' := ha.1.subcandidate
      Finset.inter_subset_right Finset.inter_subset_right hBne hYne
    have hgain := weightedMoment_child_ge hs.μ_pos.le hparent0 hselected hblue'.1 hblue'.2 hright
    have hindex : k + (t - 1) = n - 1 := by omega
    have hchild : WeightedAdmissible s k (t - 1) G B Y' := by
      refine ⟨hBC, ?_, ?_⟩
      · rw [hindex]
        exact sub_nonneg.mp hblue'.1
      · rw [bookTarget_blue_pred hs.μ_pos.ne' (by omega), hindex]
        exact (mul_le_mul_of_nonneg_left ha.2.2 hs.μ_pos.le).trans hgain
    right
    refine ⟨k, t - 1, B, Y', by omega, by omega, by omega, hchild, ?_⟩
    intro hg
    have hl := Candidate.IsGood.of_blue_extension_left hg
      Finset.inter_subset_left Finset.inter_subset_right Finset.inter_subset_right hv
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hl

theorem weightedStep_of_bounds {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (ha : WeightedAdmissible s k t G X Y) : WeightedStep s k t G X Y := by
  by_cases hY : s.rightRamseyScale k ≤ (#Y : ℝ)
  · exact weightedStep_largeRight hs (by omega) hY
  have hY' : (#Y : ℝ) < s.rightRamseyScale k := lt_of_not_ge hY
  obtain ⟨X₀, hsub, hher, ha₀⟩ := weighted_regularize hs ha
  apply WeightedStep.mono_left hsub
  have hlarge := weighted_minLeft hs hk ht ha₀ hY'
  by_cases hmany : ramseyNumber k (s.pageCliqueSize (k + t)) ≤
      #(highBlueVertices G X₀ s.highBlueRate)
  · exact weightedStep_manyHighBlue hs hk ht ha₀ hher hlarge hmany
  · exact weightedStep_fewHighBlue hs hk ht ha₀ hher hlarge (Nat.lt_of_not_ge hmany)

/-- Finite weighted candidate theorem, with every recursive graph step
constructed above. It does not yet instantiate uniform asymptotic schedules. -/
theorem weightedCandidate_of_bounds {s : WeightedData} (hs : WeightedBounds s)
    {k t : ℕ} {X Y : Finset V} (hk : 0 < k) (ht : 0 < t)
    (ha : WeightedAdmissible s k t G X Y) : Candidate.IsGood G X Y k s.rightTarget t := by
  exact weightedStrongInduction (fun hk ht ha => weightedStep_of_bounds hs hk ht ha) hk ht ha

end Ramsey3683Bootstrap
