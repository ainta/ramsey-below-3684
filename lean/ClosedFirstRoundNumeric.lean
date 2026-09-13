import ClosedFirstRound
import Mathlib.Analysis.Complex.Exponential

set_option maxRecDepth 10000
namespace Compact3684
open RamseyLean Ramsey3683Bootstrap Filter

theorem first_round_rate_bound : ProfileCheck.profile Reflected.R01.lines Reflected.R01.last 1 ≤
    (131359 / 100000 : ℝ) := by
  have hz : (Reflected.R01.lines 7602).a+(Reflected.R01.lines 7602).b ≤ 1313590000000000000 := by
    decide +kernel
  have hzR : (((Reflected.R01.lines 7602).a+(Reflected.R01.lines 7602).b : Int) : ℝ) ≤
      (1313590000000000000 : ℝ) := by exact_mod_cast hz
  have hl : (Reflected.R01.lines 7602).realLine.eval 1 ≤ (131359 / 100000 : ℝ) := by
    simp only [ProfileCheck.Line.realLine,AffineLine.eval,Log18.value,mul_one,Log18.q,Int.cast_ofNat]
    simp only [Int.cast_add] at hzR
    linarith
  exact (affineProfile_le (fun i : Fin (Reflected.R01.last+1) => (Reflected.R01.lines i.val).realLine)
    ⟨7602,by decide⟩ 1).trans hl

theorem exp_first_rate_le : Real.exp (821/625 : ℝ) ≤ 93/25 := by
  have h := Real.exp_bound' (x := (821/1250 : ℝ)) (by norm_num) (by norm_num)
    (n := 12) (by decide)
  have hb : Real.exp (821/1250 : ℝ) ≤ 19287/10000 := by
    apply h.trans
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have hp := Real.exp_pos (821/1250 : ℝ)
  rw [show (821/625 : ℝ) = 821/1250+821/1250 by norm_num,Real.exp_add]
  nlinarith

/-- A closed numerical checkpoint. The full eight-round target remains 3.68395. -/
theorem ramsey_le_372 : ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ (93/25 : ℝ)^k := by
  filter_upwards [first_round_uniform.eventually (1/100000) (by norm_num),
    eventually_gt_atTop 0] with k hk hk0
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hR := hk k hk0 le_rfl
  rw [div_self hkR] at hR
  apply hR.trans
  calc
    _ ≤ Real.exp ((821/625 : ℝ)*(k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith [first_round_rate_bound]) (Nat.cast_nonneg k)
    _ = (Real.exp (821/625 : ℝ))^k := by rw [mul_comm,Real.exp_nat_mul]
    _ ≤ (93/25 : ℝ)^k := pow_le_pow_left₀ (Real.exp_pos _).le exp_first_rate_le _

#print axioms ramsey_le_372
end Compact3684
