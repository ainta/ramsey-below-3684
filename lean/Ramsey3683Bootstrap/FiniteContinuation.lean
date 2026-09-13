import RamseyLean.Candidate
import Mathlib.Tactic

/-!
Finite continuation with an unchanged right candidate set.

These proofs use the actual RamseyLean graph and clique predicates. No abstract
"Ramsey oracle" or placeholder axiom is introduced. The asymptotic extraction
of the integer thresholds is a separate, currently unfinished module.
-/

set_option autoImplicit false

namespace Ramsey3683Bootstrap

open RamseyLean
open scoped Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An individual lower bound from every vertex on the left into the fixed
right set. Unlike a cross-density bound, it survives arbitrary left restriction. -/
def RowFloor (X Y : Finset V) (p : ℝ) : Prop :=
  ∀ v ∈ X, p * (#Y : ℝ) ≤ (#(G.neighborFinset v ∩ Y) : ℝ)

theorem RowFloor.mono_left {X X' Y : Finset V} {p : ℝ}
    (h : RowFloor G X Y p) (hXX' : X' ⊆ X) : RowFloor G X' Y p := by
  intro v hv
  exact h v (hXX' hv)

/-- The ordinary internal red-density condition, with the denominator cleared.
Loops are not counted: the normalization is `|X|(|X|-1)`, not `|X|^2`. -/
noncomputable def InternalRedAtLeast (X : Finset V) (q : ℝ) : Prop :=
  q * ((#X : ℝ) * ((#X : ℝ) - 1)) ≤
    ∑ v ∈ X, (#(G.neighborFinset v ∩ X) : ℝ)

private theorem red_blue_neighbour_card {X : Finset V} {v : V} (hv : v ∈ X) :
    #(G.neighborFinset v ∩ X) + #(Gᶜ.neighborFinset v ∩ X) = #X - 1 := by
  classical
  have hd : Disjoint (G.neighborFinset v ∩ X) (Gᶜ.neighborFinset v ∩ X) := by
    apply Finset.disjoint_left.mpr
    intro w hwR hwB
    have hr : G.Adj v w := (G.mem_neighborFinset v w).mp
      (Finset.mem_inter.mp hwR).1
    have hb : Gᶜ.Adj v w := (Gᶜ.mem_neighborFinset v w).mp
      (Finset.mem_inter.mp hwB).1
    simpa [SimpleGraph.compl_adj, hr] using hb
  have hu : (G.neighborFinset v ∩ X) ∪ (Gᶜ.neighborFinset v ∩ X) = X.erase v := by
    ext w
    by_cases hw : w = v
    · subst w
      simp
    · by_cases hr : G.Adj v w
      · simp [hw, Ne.symm hw, hr]
      · simp [hw, Ne.symm hw, hr]
  calc
    #(G.neighborFinset v ∩ X) + #(Gᶜ.neighborFinset v ∩ X) =
        #((G.neighborFinset v ∩ X) ∪ (Gᶜ.neighborFinset v ∩ X)) :=
      (Finset.card_union_of_disjoint hd).symm
    _ = #(X.erase v) := congrArg Finset.card hu
    _ = #X - 1 := Finset.card_erase_of_mem hv

private theorem red_blue_neighbour_card_real {X : Finset V} {v : V} (hv : v ∈ X) :
    (#(G.neighborFinset v ∩ X) : ℝ) + (#(Gᶜ.neighborFinset v ∩ X) : ℝ) =
      (#X : ℝ) - 1 := by
  have hpos : 0 < #X := Finset.card_pos.mpr ⟨v, hv⟩
  have h := red_blue_neighbour_card G hv
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ #X), Nat.cast_one] using hc

/-- The exact finite sparse step, including the lost pivot vertex. -/
theorem exists_blue_neighbourhood_of_not_dense {X : Finset V} {q : ℝ}
    (hX : X.Nonempty) (hnot : ¬ InternalRedAtLeast G X q) :
    ∃ v ∈ X,
      (1 - q) * ((#X : ℝ) - 1) < (#(Gᶜ.neighborFinset v ∩ X) : ℝ) := by
  classical
  by_contra hn
  push_neg at hn
  have hred : ∀ v ∈ X,
      q * ((#X : ℝ) - 1) ≤ (#(G.neighborFinset v ∩ X) : ℝ) := by
    intro v hv
    have hsplit := red_blue_neighbour_card_real G hv
    have hblue := hn v hv
    nlinarith
  have hsum := Finset.sum_le_sum (fun v hv => hred v hv)
  have hconstant :
      (∑ _v ∈ X, q * ((#X : ℝ) - 1)) =
        (#X : ℝ) * (q * ((#X : ℝ) - 1)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hconstant] at hsum
  apply hnot
  dsimp [InternalRedAtLeast]
  nlinarith

/-- Restricting to rows above a threshold produces precisely the persistent
property needed by the candidate continuation. -/
theorem rowFloor_filter (X Y : Finset V) (p : ℝ) :
    RowFloor G
      (X.filter (fun v => p * (#Y : ℝ) ≤ (#(G.neighborFinset v ∩ Y) : ℝ))) Y p := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).2

/-- A row floor implies a cross-density floor on every nonempty restriction. -/
theorem redDensity_ge_of_rowFloor {X Y : Finset V} {p : ℝ}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hrow : RowFloor G X Y p) :
    p ≤ redDensity G X Y := by
  have hs := Finset.sum_le_sum (fun v hv => hrow v hv)
  have hcount := redInteredgeCount_eq_sum_card_neighborFinset_inter (G := G) X Y
  have hcountR :
      (redInteredgeCount G X Y : ℝ) =
        ∑ v ∈ X, (#(G.neighborFinset v ∩ Y) : ℝ) := by
    exact_mod_cast hcount
  have hmul := RamseyLean.redDensity_mul_card (G := G) hX hY
  have hXp : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hYp : (0 : ℝ) < #Y := by exact_mod_cast hY.card_pos
  have hc : p * ((#X : ℝ) * (#Y : ℝ)) ≤
      redDensity G X Y * ((#X : ℝ) * (#Y : ℝ)) := by
    rw [hmul, hcountR]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_left_comm, mul_assoc] using hs
  exact (mul_le_mul_iff_left₀ (mul_pos hXp hYp)).mp hc

/-- The manuscript's finite candidate-continuation lemma.

Every dense stopping statement and every threshold inequality is an explicit
hypothesis. Thus the conclusion cannot be obtained merely by declaring a
record "valid". The upper-level certificate soundness proof must discharge
these hypotheses for each invocation.
-/
theorem finite_candidate_continuation
    (k ℓ t₀ t₁ B : ℕ) (A : ℕ → ℕ) (q : ℕ → ℝ) (p : ℝ)
    (hA : ∀ t, 0 < A t)
    (hq : ∀ t, t₀ < t → t ≤ t₁ → q t < 1)
    (hbase : ∀ X Y : Finset V, Candidate G X Y → RowFloor G X Y p →
      A t₀ ≤ #X → B ≤ #Y → Candidate.IsGood G X Y k ℓ t₀)
    (hstop : ∀ t, t₀ < t → t ≤ t₁ → ∀ X : Finset V,
      A t ≤ #X → InternalRedAtLeast G X (q t) →
        hasRedClique G X k ∨ hasBlueClique G X t)
    (hstep : ∀ t, t₀ < t → t ≤ t₁ →
      (A (t - 1) : ℝ) ≤ (1 - q t) * ((A t : ℝ) - 1)) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → ∀ X Y : Finset V,
      Candidate G X Y → RowFloor G X Y p → A t ≤ #X → B ≤ #Y →
        Candidate.IsGood G X Y k ℓ t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht₀ ht₁ X Y hcan hrow hX hY
    by_cases heq : t = t₀
    · subst t
      exact hbase X Y hcan hrow hX hY
    have hgt : t₀ < t := by omega
    have htpos : 1 ≤ t := by omega
    by_cases hdense : InternalRedAtLeast G X (q t)
    · rcases hstop t hgt ht₁ X hX hdense with hred | hblue
      · exact Candidate.IsGood.of_red
          (hasRedClique_mono Finset.subset_union_left hred)
      · exact Candidate.IsGood.of_blue_left hblue
    · obtain ⟨v, hv, hblue⟩ :=
        exists_blue_neighbourhood_of_not_dense G hcan.left_nonempty hdense
      let T : Finset V := Gᶜ.neighborFinset v ∩ X
      have hXreal : (A t : ℝ) ≤ (#X : ℝ) := by exact_mod_cast hX
      have hqpos : 0 ≤ 1 - q t := by linarith [hq t hgt ht₁]
      have hcardReal : (A (t - 1) : ℝ) ≤ (#T : ℝ) := by
        calc
          (A (t - 1) : ℝ) ≤ (1 - q t) * ((A t : ℝ) - 1) := hstep t hgt ht₁
          _ ≤ (1 - q t) * ((#X : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hqpos
          _ ≤ (#T : ℝ) := hblue.le
      have hcard : A (t - 1) ≤ #T := by exact_mod_cast hcardReal
      have hTnonempty : T.Nonempty :=
        Finset.card_pos.mp (lt_of_lt_of_le (hA (t - 1)) hcard)
      have hTX : T ⊆ X := Finset.inter_subset_right
      have hTcan : Candidate G T Y :=
        hcan.subcandidate hTX (by intro z hz; exact hz) hTnonempty hcan.right_nonempty
      have hTrow : RowFloor G T Y p := RowFloor.mono_left G hrow hTX
      have hsmall : Candidate.IsGood G T Y k ℓ (t - 1) :=
        ih (t - 1) (by omega) (by omega) (by omega)
          T Y hTcan hTrow hcard hY
      have hext := hsmall.of_blue_extension_left
        (hneighbor := Finset.inter_subset_left)
        (hX := hTX) (hY := by intro z hz; exact hz) (hv := hv)
      simpa only [Nat.sub_add_cancel htpos] using hext

end Ramsey3683Bootstrap
