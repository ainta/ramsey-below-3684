import Ramsey3683Bootstrap.TerminalTransfer
import TerminalNumeric

namespace Compact3684
open RamseyLean Ramsey3683Bootstrap Filter

/-- The remaining premise is exactly the finite certificate's global affine
profile. The terminal graph transfer and numerical comparison are proved. -/
theorem below_3684_of_affine
    (h : UniformRamseyExpBound (fun r => affineA + affineD * r)) :
    ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ (921 / 250 : ℝ) ^ k := by
  apply diagonal_lt_base_of_uniform h (by norm_num [affineA])
    ?_ terminal_numeric_lt
  have hb := Real.quadratic_le_exp_of_nonneg (by norm_num [affineD] : 0 ≤ affineD)
  norm_num [affineD] at hb ⊢
  linarith

#print axioms below_3684_of_affine
end Compact3684
