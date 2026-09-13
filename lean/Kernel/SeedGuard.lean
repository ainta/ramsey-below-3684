import Kernel.Log18

/-! Integer-only guards used by the reflected certificate. No real-valued
decision procedures and no trusted numerical evaluator occur here. -/
set_option autoImplicit false
namespace Compact3684.Certificate
open Compact3684.Log18 (CatalogEntry scale q)

def unit : Int := 1000000000000000000000000000000
def valueScale (N : Nat) : Int := N*unit

structure Seed where
  a : Int
  b : Int
  theta : Int
  mu : Int
  pi : Int
  deriving DecidableEq, Repr

def densityNumerator (s : Seed) (logOneMinusMu logPi : Int) : Int :=
  (scale-s.mu)*(s.a*q+s.theta*logOneMinusMu)+scale*scale*logPi

def budgetNumerator (s : Seed) (N i j : Nat) (u v logMu : Int) : Int :=
  s.theta*u*q+v*scale*q-s.a*valueScale N*q-(j : Int)*s.b*unit*q+
    s.theta*(i : Int)*logMu*unit

def seedGuard (s : Seed) (N i j : Nat) (u v : Int)
    (logMu logOneMinusMu logPi : CatalogEntry) : Bool :=
  decide (0 < N ∧ 0 < i ∧ i ≤ j ∧ j ≤ N ∧
    0 < s.theta ∧ 0 < s.mu ∧ s.mu < scale ∧ 0 < s.pi ∧ s.pi < scale ∧
    logMu.argument = s.mu ∧ logOneMinusMu.argument = scale-s.mu ∧ logPi.argument = s.pi ∧
    0 < densityNumerator s logOneMinusMu.lo logPi.lo ∧
    0 < budgetNumerator s N i j u v logMu.lo)

def blueGuard (cost p : Int) (logOneMinusP : CatalogEntry) : Bool :=
  decide (0 < cost ∧ 0 < p ∧ p < scale ∧ logOneMinusP.argument = scale-p ∧
    0 < cost*q+scale*logOneMinusP.lo)

end Compact3684.Certificate
