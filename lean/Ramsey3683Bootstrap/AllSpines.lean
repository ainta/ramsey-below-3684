import Ramsey3683Bootstrap.MaximumClique
import Ramsey3683Bootstrap.MinimumDegreeCore
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Sum over every spine of a maximum clique. This finite identity avoids
binomial asymptotics in the terminal transfer. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sum_weighted_commonRedNeighbors (S X : Finset V) (z : ℝ) :
    (∑ A ∈ S.powerset, z ^ #A * (#(commonRedNeighbors G A X) : ℝ)) =
      ∑ v ∈ X, (1 + z) ^ #(G.neighborFinset v ∩ S) := by
  classical
  have hcard (A : Finset V) : (#(commonRedNeighbors G A X) : ℝ) =
      ∑ v ∈ X, if A ⊆ G.neighborFinset v then (1 : ℝ) else 0 := by
    simp only [commonRedNeighbors, Finset.card_eq_sum_ones, Nat.cast_sum,
      Nat.cast_one, Finset.sum_filter, apply_ite, Nat.cast_zero]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : S.powerset.filter (fun A => A ⊆ G.neighborFinset v) =
      (G.neighborFinset v ∩ S).powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
    tauto
  rw [hfilter]
  simpa only [Finset.prod_const] using
    (Finset.prod_one_add (f := fun _ : V => z) (G.neighborFinset v ∩ S)).symm

theorem exp_average_lower {X : Finset V} (hX : X.Nonempty)
    (f : V → ℝ) {α t : ℝ} (ht : 0 ≤ t)
    (havg : α * (#X : ℝ) ≤ ∑ v ∈ X, f v) :
    (#X : ℝ) * Real.exp (t * α) ≤ ∑ v ∈ X, Real.exp (t * f v) := by
  have hn : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hw : ∑ _v ∈ X, (1 / (#X : ℝ)) = 1 := by simp [ne_of_gt hn]
  have hj := convexOn_exp.map_sum_le (t := X)
    (w := fun _ => 1 / (#X : ℝ)) (p := fun v => t * f v)
    (by intro v hv; positivity) hw (by intro v hv; trivial)
  simp only [smul_eq_mul] at hj
  have ha : t * α ≤ ∑ v ∈ X, (1 / (#X : ℝ)) * (t * f v) := by
    rw [show (∑ v ∈ X, (1 / (#X : ℝ)) * (t * f v)) =
      t * ((∑ v ∈ X, f v) / (#X : ℝ)) by
        simp_rw [show ∀ v, (1 / (#X : ℝ)) * (t * f v) =
          t * (f v / (#X : ℝ)) from fun v => by ring]
        rw [← Finset.mul_sum, ← Finset.sum_div]]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hn).mpr havg) ht
  have h := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr ha).trans hj) hn.le
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      field_simp

theorem MaximumRedClique.page_ramsey_bound {W S X A : Finset V} {k : ℕ}
    (hS : MaximumRedClique G W S) (hXW : X ⊆ W) (hAS : A ⊆ S)
    (hnoBlue : ¬ hasBlueClique G W k) :
    #(commonRedNeighbors G A X) < ramseyNumber (#S - #A + 1) k := by
  by_contra hn
  have hR := (ramseyNumber_spec (#S - #A + 1) k).mono (le_of_not_gt hn)
  rcases hR.on_finset G (commonRedNeighbors G A X) rfl with hr | hb
  · exact MaximumRedClique.page_no_red G hS hAS hXW hr
  · exact hnoBlue (hasBlueClique_mono ((Finset.filter_subset _ _).trans hXW) hb)

theorem MaximumRedClique.all_spines_upper {W S X : Finset V} {k : ℕ}
    {C B z : ℝ} (hS : MaximumRedClique G W S) (hXW : X ⊆ W)
    (hnoBlue : ¬ hasBlueClique G W k) (hz : 0 ≤ z)
    (hR : ∀ r : ℕ, 0 < r → r ≤ #S + 1 →
      (ramseyNumber r k : ℝ) ≤ C * B ^ r) :
    (∑ v ∈ X, (1 + z) ^ #(G.neighborFinset v ∩ S)) ≤
      C * B * (B + z) ^ #S := by
  rw [← sum_weighted_commonRedNeighbors G S X z]
  calc
    (∑ A ∈ S.powerset, z ^ #A * (#(commonRedNeighbors G A X) : ℝ)) ≤
        ∑ A ∈ S.powerset, z ^ #A * (C * B ^ (#S - #A + 1)) := by
      apply Finset.sum_le_sum
      intro A hA
      have ha := Finset.mem_powerset.mp hA
      have hp : (#(commonRedNeighbors G A X) : ℝ) ≤
          (ramseyNumber (#S - #A + 1) k : ℝ) := by
        exact_mod_cast (MaximumRedClique.page_ramsey_bound G hS hXW ha hnoBlue).le
      exact mul_le_mul_of_nonneg_left
        (hp.trans (hR _ (by omega) (by omega))) (pow_nonneg hz _)
    _ = C * B * (B + z) ^ #S := by
      simp_rw [pow_succ]
      calc
        _ = C * B * ∑ A ∈ S.powerset, z ^ #A * B ^ (#S - #A) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A hA
          ring
        _ = _ := by rw [Finset.sum_pow_mul_eq_add_pow, add_comm z B]

theorem MaximumRedClique.all_spines_transfer {W S X : Finset V} {k : ℕ}
    {C B s : ℝ} (hS : MaximumRedClique G W S) (hXW : X ⊆ W)
    (hX : X.Nonempty) (hnoBlue : ¬ hasBlueClique G W k) (hs : 1 ≤ s)
    (havg : ((#S : ℝ) / 2 - 1) * (#X : ℝ) ≤
      ∑ v ∈ X, (#(G.neighborFinset v ∩ S) : ℝ))
    (hR : ∀ r : ℕ, 0 < r → r ≤ #S + 1 →
      (ramseyNumber r k : ℝ) ≤ C * B ^ r) :
    (#X : ℝ) * s ^ #S ≤ C * B * s ^ 2 * (B + s ^ 2 - 1) ^ #S := by
  have hs0 : 0 < s := by linarith
  have hz : 0 ≤ s ^ 2 - 1 := by nlinarith
  have hlo := exp_average_lower hX (fun v => (#(G.neighborFinset v ∩ S) : ℝ))
    (t := 2 * Real.log s) (by positivity [Real.log_nonneg hs]) havg
  have hexp (n : ℕ) : Real.exp (2 * Real.log s * (n : ℝ)) = (s ^ 2) ^ n := by
    rw [show 2 * Real.log s * (n : ℝ) = (n : ℝ) * (2 * Real.log s) by ring,
      Real.exp_nat_mul]
    congr 1
    simpa using (Real.exp_nat_mul (Real.log s) 2).trans (by rw [Real.exp_log hs0])
  simp_rw [hexp] at hlo
  have hup := MaximumRedClique.all_spines_upper G hS hXW hnoBlue hz hR
  rw [show 1 + (s ^ 2 - 1) = s ^ 2 by ring] at hup
  have h := mul_le_mul_of_nonneg_right (hlo.trans hup) (sq_nonneg s)
  have he : Real.exp (2 * Real.log s * ((#S : ℝ) / 2 - 1)) * s ^ 2 = s ^ #S := by
    rw [← Real.exp_log hs0, ← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_nat_mul (Real.log (Real.exp (Real.log s))) #S using 1 <;>
      simp only [Real.log_exp] <;> ring
  calc
    _ = ((#X : ℝ) * Real.exp (2 * Real.log s * ((#S : ℝ) / 2 - 1))) * s ^ 2 := by
      rw [mul_assoc, he]
    _ ≤ _ := h
    _ = _ := by ring

#print axioms sum_weighted_commonRedNeighbors
#print axioms exp_average_lower
#print axioms MaximumRedClique.all_spines_upper
#print axioms MaximumRedClique.all_spines_transfer
end Ramsey3683Bootstrap
