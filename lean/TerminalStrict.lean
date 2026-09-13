import TerminalTarget
import Ramsey3683Bootstrap.ProfileCheck
import Kernel.TerminalSupport

set_option autoImplicit false
namespace Compact3684
open RamseyLean Ramsey3683Bootstrap Filter

theorem terminal_numeric_lt_368395 :
    2 * Real.exp affineA * Real.sqrt (Real.exp affineD - 1) < 73679 / 20000 := by
  have ha := exp_affineA_le
  have hd := exp_affineD_le
  have ha0 := Real.exp_pos affineA
  have hd0 : 0 ≤ Real.exp affineD - 1 := by
    have h := Real.add_one_le_exp affineD
    have : 0 ≤ affineD := by norm_num [affineD]
    linarith
  have ha2 : (Real.exp affineA)^2 ≤ (17228847 / 10000000 : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul ha2 (sub_le_sub_right hd 1) hd0
    (sq_nonneg (17228847 / 10000000 : ℝ))
  have hsquare :
      (2 * Real.exp affineA * Real.sqrt (Real.exp affineD - 1))^2 <
        (73679 / 20000 : ℝ)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hd0]
    calc
      2^2 * (Real.exp affineA)^2 * (Real.exp affineD - 1)
          ≤ 4 * (17228847 / 10000000 : ℝ)^2 * (21429857 / 10000000 - 1) := by
            nlinarith only [hprod]
      _ < (73679 / 20000 : ℝ)^2 := by norm_num
  by_contra hn
  have hge := le_of_not_gt hn
  nlinarith only [hsquare,hge]

theorem below_368395_of_affine
    (h : UniformRamseyExpBound (fun r => affineA+affineD*r)) :
    ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ (73679 / 20000 : ℝ)^k := by
  apply diagonal_lt_base_of_uniform h (by norm_num [affineA])
    ?_ terminal_numeric_lt_368395
  have hb := Real.quadratic_le_exp_of_nonneg (by norm_num [affineD] : 0 ≤ affineD)
  norm_num [affineD] at hb ⊢
  linarith

theorem affine_of_final_profile
    (h : UniformRamseyExpBound (ProfileCheck.profile Reflected.R08.lines Reflected.R08.last)) :
    UniformRamseyExpBound (fun r => affineA+affineD*r) := by
  apply h.weakenRate
  intro r hr
  have hs := ProfileCheck.supportGuard_sound TerminalSupport.checked
    (show r ∈ Set.Icc (0 : ℝ) 1 from ⟨hr.1.le,hr.2⟩)
  norm_num [Log18.value,Log18.q,affineA,affineD] at hs ⊢
  exact hs

#print axioms terminal_numeric_lt_368395
#print axioms affine_of_final_profile
#print axioms below_368395_of_affine
end Compact3684
