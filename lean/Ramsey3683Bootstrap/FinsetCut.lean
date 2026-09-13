import Ramsey3683Bootstrap.GridSemantics

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem excess_singleton (p : ℝ) (v : V) : excess G p {v} {v} = -p := by
  have hc : redInteredgeCount G {v} {v} = 0 := by
    rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
    simp
  simp [excess, hc]

private theorem adjusted_excess_insert {W : Finset V} {v : V} (hv : v ∉ W) (p : ℝ) :
    excess G p (insert v W) (insert v W) + p * (#(insert v W) : ℝ) =
      excess G p W W + p * (#W : ℝ) + 2 * excess G p {v} W := by
  have hd : Disjoint ({v} : Finset V) W := by simpa using hv
  have he : excess G p (insert v W) (insert v W) =
      excess G p W W + 2 * excess G p {v} W - p := by
    rw [← Finset.singleton_union]
    rw [excess_union_left hd, excess_union_right ({v} : Finset V) hd,
      excess_union_right W hd, excess_comm p W ({v} : Finset V), excess_singleton]
    ring
  rw [he, Finset.card_insert_of_notMem hv]
  push_cast
  ring

/-- The upstream excess-cut argument, generalized to an arbitrary finset so
later semantic rules do not need to change the vertex type. -/
theorem exists_finset_excess_cut (W : Finset V) (p : ℝ) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = W ∧
      (excess G p W W + p * (#W : ℝ)) / 4 ≤ excess G p A B := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨∅, ∅, by simp, by simp, by simp [excess]⟩
  | @insert v W hv ih =>
    obtain ⟨A, B, hd, hAB, hcut⟩ := ih
    have hvA : v ∉ A := fun h => hv (hAB ▸ Finset.mem_union_left B h)
    have hvB : v ∉ B := fun h => hv (hAB ▸ Finset.mem_union_right A h)
    have hdA : Disjoint ({v} : Finset V) A := by simpa using hvA
    have hdB : Disjoint ({v} : Finset V) B := by simpa using hvB
    have hsplit : excess G p {v} W = excess G p {v} A + excess G p {v} B := by
      rw [← hAB, excess_union_right ({v} : Finset V) hd]
    by_cases h : excess G p {v} A ≤ excess G p {v} B
    · refine ⟨insert v A, B, by simpa using And.intro hvB hd, ?_, ?_⟩
      · rw [Finset.insert_union, hAB]
      · rw [adjusted_excess_insert G hv p, hsplit]
        have he : excess G p (insert v A) B = excess G p {v} B + excess G p A B := by
          rw [← Finset.singleton_union, excess_union_left hdA]
        rw [he]
        linarith
    · refine ⟨A, insert v B, by simpa using And.intro hvA hd, ?_, ?_⟩
      · rw [Finset.union_insert, hAB]
      · rw [adjusted_excess_insert G hv p, hsplit]
        have he : excess G p A (insert v B) = excess G p {v} A + excess G p A B := by
          rw [← Finset.singleton_union, excess_union_right A hdB, excess_comm p A ({v} : Finset V)]
        rw [he]
        linarith

theorem exists_large_dense_cut {W : Finset V} {q p : ℝ}
    (hq : 0 ≤ q) (hqp : q < p) (hW : 2 ≤ #W) (hd : InternalRedAtLeast G W p) :
    ∃ A B : Finset V, A ∪ B = W ∧ Candidate G A B ∧ q ≤ redDensity G A B ∧
      ((p - q) / 8) * (#W : ℝ) ≤ (#A : ℝ) ∧
      ((p - q) / 8) * (#W : ℝ) ≤ (#B : ℝ) := by
  classical
  obtain ⟨A, B, hAB, hcover, hcut⟩ := exists_finset_excess_cut G W q
  have hn : (2 : ℝ) ≤ #W := by exact_mod_cast hW
  have hnp : (0 : ℝ) < #W := by linarith
  have hδ : 0 < p - q := sub_pos.mpr hqp
  have hcount : p * ((#W : ℝ) * ((#W : ℝ) - 1)) ≤ (redInteredgeCount G W W : ℝ) := by
    rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
    push_cast
    exact hd
  have hlarge : ((p - q) / 8) * (#W : ℝ) ^ 2 ≤ excess G q A B := by
    have hprod : (0 : ℝ) ≤ (p - q) * ((#W : ℝ) * ((#W : ℝ) - 2)) := by positivity
    unfold excess at hcut ⊢
    nlinarith
  have hepos : 0 < excess G q A B :=
    (mul_pos (div_pos hδ (by norm_num)) (sq_pos_of_pos hnp)).trans_le hlarge
  have hc : Candidate G A B := Candidate.of_disjoint_of_excess_pos hAB hepos
  have hAp : (0 : ℝ) < #A := by exact_mod_cast hc.left_card_pos
  have hBp : (0 : ℝ) < #B := by exact_mod_cast hc.right_card_pos
  have hAd : (#A : ℝ) ≤ #W := by exact_mod_cast (Finset.card_le_card
    (show A ⊆ W from hcover ▸ Finset.subset_union_left))
  have hBd : (#B : ℝ) ≤ #W := by exact_mod_cast (Finset.card_le_card
    (show B ⊆ W from hcover ▸ Finset.subset_union_right))
  have hprod : excess G q A B ≤ (#A : ℝ) * (#B : ℝ) := by
    have hred : (redInteredgeCount G A B : ℝ) ≤ (#A : ℝ) * (#B : ℝ) := by
      exact_mod_cast redInteredgeCount_le_mul (G := G) A B
    unfold excess
    nlinarith [mul_nonneg hq (mul_nonneg hAp.le hBp.le)]
  have hdensity : q ≤ redDensity G A B := by
    rw [hc.excess_eq_density_sub_mul q] at hepos
    have hp := (mul_pos_iff_of_pos_right (mul_pos hAp hBp)).mp hepos
    exact (sub_pos.mp hp).le
  refine ⟨A, B, hcover, hc, hdensity, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hBd hAp.le
    nlinarith [hlarge.trans hprod]
  · have hm := mul_le_mul_of_nonneg_right hAd hBp.le
    nlinarith [hlarge.trans hprod]

end Ramsey3683Bootstrap
