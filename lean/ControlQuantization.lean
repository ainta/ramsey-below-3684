import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! Algebraic justification for sharing logarithm enclosures after an affine
lift. Graph-theoretic soundness and full certificate execution are separate. -/
set_option autoImplicit false
namespace Compact3684

/-- Adding eps*t to a profile preserves both support orientations after
adding eps to b only. This uses t≤1, not a hidden symmetry assumption. -/
theorem support_affine_lift {a b e t eps : ℝ} (ht : t ≤ 1) (heps : 0 ≤ eps)
    (hfirst : e ≤ a+t*b) (hsecond : e ≤ b+t*a) :
    e+eps*t ≤ a+t*(b+eps) ∧ e+eps*t ≤ b+eps+t*a := by
  constructor <;> nlinarith

/-- Rounding mu down only increases the weighted density exponent whenever
the original density exponent is nonnegative. No derivative estimate is needed. -/
theorem density_exponent_mono {a theta mu small : ℝ}
    (htheta : 0 ≤ theta) (hmu : small ≤ mu) (hpos : 0 < 1-mu)
    (hinner : 0 ≤ a+theta*Real.log (1-mu)) :
    (1-mu)*(a+theta*Real.log (1-mu)) ≤
      (1-small)*(a+theta*Real.log (1-small)) := by
  have hz : 1-mu ≤ 1-small := by linarith
  have hl := Real.log_le_log hpos hz
  have hi := add_le_add_left (mul_le_mul_of_nonneg_left hl htheta) a
  have hi' : a+theta*Real.log (1-mu) ≤ a+theta*Real.log (1-small) := by
    linarith [hi]
  exact mul_le_mul hz hi' hinner (by linarith)

/-- The affine lift pays for a controlled downward change in log(mu). -/
theorem weighted_budget_lift {a b theta alpha t u v eps h oldLog newLog : ℝ}
    (htheta : 0 ≤ theta) (halpha : 0 ≤ alpha) (heps : h ≤ eps)
    (hlog : oldLog-h ≤ newLog) :
    theta*u+v-a-t*b+theta*alpha*oldLog ≤
      theta*(u+eps*alpha)+(v+eps*t)-a-t*(b+eps)+theta*alpha*newLog := by
  have hgain : 0 ≤ theta*alpha*(eps+newLog-oldLog) :=
    mul_nonneg (mul_nonneg htheta halpha) (by linarith)
  nlinarith only [hgain]

/-- The same small relative-grid error is paid for in the blue cost. -/
theorem blue_budget_lift {cost oldLog newLog eps h : ℝ}
    (hblue : 0 < cost+oldLog) (heps : h ≤ eps)
    (hlog : oldLog-h ≤ newLog) : 0 < cost+eps+newLog := by linarith

#print axioms support_affine_lift
#print axioms density_exponent_mono
#print axioms weighted_budget_lift
#print axioms blue_budget_lift
end Compact3684
