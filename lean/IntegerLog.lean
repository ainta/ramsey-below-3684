import Std

/-! Executable exact arithmetic for a bounded KERNEL COMPUTATION benchmark.
This file does NOT prove that its intervals enclose the real logarithm.
Such a soundness theorem is required before using it in a Ramsey proof. -/
set_option autoImplicit false
namespace Compact3684.Bench

def q : Int := 10000000000000000000000000000000000000000
def scale : Int := 1000000000000
def ceilDiv (a b : Int) : Int := -((-a) / b)
abbrev Interval := Int × Int
def rat (n d : Int) : Interval := (n*q/d, ceilDiv (n*q) d)
def plus (a b : Interval) : Interval := (a.1+b.1, a.2+b.2)
def timesPos (a b : Interval) : Interval :=
  (a.1*b.1/q, ceilDiv (a.2*b.2) q)
def divide (a : Interval) (d : Int) : Interval := (a.1/d, ceilDiv a.2 d)
def timesInt (a : Interval) (k : Int) : Interval :=
  if k ≥ 0 then (k*a.1, k*a.2) else (k*a.2, k*a.1)

def series (u2 : Interval) : Nat → Nat → Interval → Interval → Interval
  | 0, _, _, total => (2*total.1, 2*total.2+1)
  | count+1, j, w, total =>
      series u2 count (j+1) (timesPos w u2) (plus total (divide w (2*j+1)))
def reduced (n d : Int) : Interval :=
  let u := rat (n-d) (n+d)
  series (timesPos u u) 50 0 u (0,0)

def logTwoBounds : Interval :=
  (6931471805599453094172321214581765680718,
   6931471805599453094172321214581765680819)

/-- Share the proof of the constant rather than recomputing its series at
every rational logarithm. This is exact kernel-checked integer equality. -/
theorem logTwoBounds_correct : reduced 2 1 = logTwoBounds := by decide

def normalize : Nat → Int → Int → Int → Option (Int × Int × Int)
  | 0, _, _, _ => none
  | fuel+1, n, d, k =>
      if n < d then normalize fuel (2*n) d (k-1)
      else if n ≥ 2*d then normalize fuel n (2*d) (k+1)
      else some (n,d,k)

def logarithm (n d : Int) : Option Interval :=
  if n ≤ 0 ∨ d ≤ 0 then none else
  match normalize 128 n d 0 with
  | none => none
  | some (nn,dd,k) => some (plus (reduced nn dd) (timesInt logTwoBounds k))

def blueGuard (cost density : Int) : Bool :=
  if cost ≤ 0 ∨ density ≤ 0 ∨ density ≥ scale then false else
  match logarithm (scale-density) scale with
  | none => false
  | some l => decide (0 < (rat cost scale).1 + l.1)

end Compact3684.Bench
