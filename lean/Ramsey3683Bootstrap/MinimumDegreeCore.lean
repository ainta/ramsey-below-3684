import RamseyLean.Counting
import Ramsey3683Bootstrap.FiniteContinuation
import Mathlib.Tactic

/-!
Finite minimum-degree core via maximization of edge excess.
This avoids formalizing an iterative vertex-deletion algorithm.
The normalization uses ordered internal edges, so the exact vertex-deletion
correction is p/2. The asymptotic application must still absorb that correction.
-/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Among subsets of W, maximize e_R(C,C) - p |C|². Removing any vertex
cannot increase this quantity, giving a pointwise degree floor. -/
theorem exists_max_excess_core (W : Finset V) (p : ℝ) :
    ∃ C : Finset V, C ⊆ W ∧
      excess G p W W ≤ excess G p C C ∧
      (∀ v ∈ C, p * ((#C : ℝ) - 1 / 2) ≤ (#(G.neighborFinset v ∩ C) : ℝ)) ∧
      excess G p W W ≤ (1 - p) * (#C : ℝ) ^ 2 := by
  classical
  have hne : W.powerset.Nonempty := ⟨∅, by simp⟩
  obtain ⟨C, hCW, hmax⟩ := Finset.exists_max_image W.powerset
    (fun C : Finset V => excess G p C C) hne
  have hsub : C ⊆ W := Finset.mem_powerset.mp hCW
  have hW : excess G p W W ≤ excess G p C C := hmax W (by simp)
  refine ⟨C, hsub, hW, ?_, ?_⟩
  · intro v hv
    let T := C.erase v
    have hTC : T ⊆ C := Finset.erase_subset v C
    have hTmax : excess G p T T ≤ excess G p C C :=
      hmax T (Finset.mem_powerset.mpr (hTC.trans hsub))
    have hdisj : Disjoint ({v} : Finset V) T := by simp [T]
    have hunion : ({v} : Finset V) ∪ T = C := by
      simpa [T] using Finset.insert_erase hv
    have hcardNat : #T + 1 = #C := by
      have hc : 0 < #C := Finset.card_pos.mpr ⟨v, hv⟩
      simp only [T, Finset.card_erase_of_mem hv]
      omega
    have hcard : (#T : ℝ) + 1 = (#C : ℝ) := by exact_mod_cast hcardNat
    have hneigh : G.neighborFinset v ∩ T = G.neighborFinset v ∩ C := by
      ext w
      simp only [T, Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hn, _hne, hw⟩
        exact ⟨hn, hw⟩
      · rintro ⟨hn, hw⟩
        refine ⟨hn, ?_, hw⟩
        intro he
        subst w
        simpa using hn
    have hcross : redInteredgeCount G {v} T = #(G.neighborFinset v ∩ C) := by
      rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
      simp [hneigh]
    have hself : redInteredgeCount G {v} {v} = 0 := by
      rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
      simp
    have he : excess G p C C = excess G p T T +
        2 * excess G p {v} T + excess G p {v} {v} := by
      conv_lhs => rw [← hunion]
      rw [excess_union_left hdisj,
          excess_union_right ({v} : Finset V) hdisj,
          excess_union_right T hdisj,
          excess_comm p T ({v} : Finset V)]
      ring
    have hecross : excess G p {v} T =
        (#(G.neighborFinset v ∩ C) : ℝ) - p * (#T : ℝ) := by
      simp [excess, hcross]
    have heself : excess G p {v} {v} = -p := by simp [excess, hself]
    rw [hecross, heself] at he
    rw [← hcard]
    nlinarith
  · have hcount : (redInteredgeCount G C C : ℝ) ≤ (#C : ℝ) * (#C : ℝ) := by
      exact_mod_cast redInteredgeCount_le_mul (G := G) C C
    apply hW.trans
    unfold excess
    nlinarith

/-- Input in ordinary internal-density normalization |W|(|W|-1).
The size conclusion remains division-free and exact. -/
theorem exists_large_degree_core {W : Finset V} {p p₀ : ℝ}
    (hd : InternalRedAtLeast G W p₀) :
    ∃ C : Finset V, C ⊆ W ∧
      (p₀ - p) * (#W : ℝ) ^ 2 - p₀ * (#W : ℝ) ≤
        (1 - p) * (#C : ℝ) ^ 2 ∧
      (∀ v ∈ C, p * ((#C : ℝ) - 1 / 2) ≤ (#(G.neighborFinset v ∩ C) : ℝ)) := by
  obtain ⟨C, hsub, hmax, hdegree, hbound⟩ := exists_max_excess_core G W p
  have hcount : p₀ * ((#W : ℝ) * ((#W : ℝ) - 1)) ≤
      (redInteredgeCount G W W : ℝ) := by
    change _ ≤ (redInteredgeCount G W W : ℝ)
    rw [redInteredgeCount_eq_sum_card_neighborFinset_inter]
    push_cast
    exact hd
  have hlo : (p₀ - p) * (#W : ℝ) ^ 2 - p₀ * (#W : ℝ) ≤ excess G p W W := by
    unfold excess
    nlinarith
  exact ⟨C, hsub, hlo.trans hbound, hdegree⟩

/-- Removing the exact p/2 rounding term is justified only once the core
has the displayed size. It is not discarded inside the graph argument. -/
theorem core_degree_floor {C : Finset V} {p q : ℝ}
    (hdegree : ∀ v ∈ C, p * ((#C : ℝ) - 1 / 2) ≤ (#(G.neighborFinset v ∩ C) : ℝ))
    (hsize : p ≤ 2 * (p - q) * (#C : ℝ)) :
    ∀ v ∈ C, q * (#C : ℝ) ≤ (#(G.neighborFinset v ∩ C) : ℝ) := by
  intro v hv
  have h := hdegree v hv
  nlinarith

end Ramsey3683Bootstrap

