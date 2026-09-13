import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
A small, kernel-checked terminal numerical inequality with deliberately
rounded UP affine coefficients. This file does not assert that those
coefficients bound Ramsey numbers: the graph/certificate bridge is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Compact3684

noncomputable def affineA : ℝ := 544 / 1000
noncomputable def affineD : ℝ := 7622 / 10000

theorem exp_affineA_le : Real.exp affineA ≤ 17228847 / 10000000 := by
  have h := Real.exp_bound' (x := affineA) (by norm_num [affineA])
    (by norm_num [affineA]) (n := 12) (by decide)
  apply h.trans
  norm_num [affineA, Finset.sum_range_succ, Nat.factorial]

theorem exp_affineD_le : Real.exp affineD ≤ 21429857 / 10000000 := by
  have h := Real.exp_bound' (x := affineD) (by norm_num [affineD])
    (by norm_num [affineD]) (n := 12) (by decide)
  apply h.trans
  norm_num [affineD, Finset.sum_range_succ, Nat.factorial]

/-- The final comparison is a real-analysis theorem, not a floating-point
calculation or an assumed certificate result. -/
theorem terminal_numeric_lt :
    2 * Real.exp affineA * Real.sqrt (Real.exp affineD - 1) < 921 / 250 := by
  have ha := exp_affineA_le
  have hd := exp_affineD_le
  have ha0 := Real.exp_pos affineA
  have hd0 : 0 ≤ Real.exp affineD - 1 := by
    have h := Real.add_one_le_exp affineD
    have : 0 ≤ affineD := by norm_num [affineD]
    linarith
  have ha2 : (Real.exp affineA)^2 ≤ (17228847 / 10000000 : ℝ)^2 := by
    nlinarith
  have hprod := mul_le_mul ha2 (sub_le_sub_right hd 1) hd0
    (sq_nonneg (17228847 / 10000000 : ℝ))
  have hsquare :
      (2 * Real.exp affineA * Real.sqrt (Real.exp affineD - 1))^2 <
        (921 / 250 : ℝ)^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hd0]
    calc
      2^2 * (Real.exp affineA)^2 * (Real.exp affineD - 1)
          ≤ 4 * (17228847 / 10000000 : ℝ)^2 * (21429857 / 10000000 - 1) := by
            nlinarith only [hprod]
      _ < (921 / 250 : ℝ)^2 := by norm_num
  by_contra hn
  have hge := le_of_not_gt hn
  nlinarith only [hsquare, hge]

#print axioms exp_affineA_le
#print axioms exp_affineD_le
#print axioms terminal_numeric_lt

end Compact3684
