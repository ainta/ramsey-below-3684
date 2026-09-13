import Kernel.Log18

set_option autoImplicit false
namespace Compact3684.Elementary
open Compact3684.Log18

def timesRat (a : Interval) (n d : Int) : Interval := divide (timesInt a n) d
def minus (a b : Interval) : Interval := plus a (timesInt b (-1))

def expSeries (t : Interval) : Nat → Nat → Interval → Interval → Interval
  | 0, _, _, total => (total.1-1,total.2+1)
  | count+1, j, w, total =>
      expSeries t count (j+1) (divide (timesPos w t) (j+1))
        (plus total (timesInt w ((-1 : Int)^j)))

def expNeg (n d : Int) : Interval := expSeries (rat n d) 20 0 (q,q) (0,0)

def initialValueSlope (n d : Int) : Option (Interval × Interval) := do
  if n ≤ 0 ∨ d ≤ 0 ∨ d < n then none else
  let lt ← logarithm n d
  let l1t ← logarithm (d+n) d
  let lratio ← logarithm (d+n) n
  let e := expNeg n d
  let poly := -25*n*d^2+3*n^2*d+8*n^3
  let derivativePoly := -25*d^3+31*n*d^2+21*n^2*d-8*n^3
  let val := plus (minus (timesRat l1t (d+n) d) (timesRat lt n d))
    (timesRat e poly (100*d^3))
  let slope := plus lratio (timesRat e derivativePoly (100*d^3))
  pure (val,slope)

def tangentGuard (n d an ad bn bd : Int) : Bool :=
  if ad ≤ 0 ∨ bd ≤ 0 then false else
  match initialValueSlope n d with
  | none => false
  | some (val,slope) =>
      let atZero := minus val (timesRat slope n d)
      let atOne := plus val (timesRat slope (d-n) d)
      decide (atZero.2 ≤ (rat an ad).1 ∧ atOne.2 ≤ (plus (rat an ad) (rat bn bd)).1)

structure InitialLine where
  n : Int
  d : Int
  intercept : Int
  slope : Int
  deriving DecidableEq, Repr

def initialLineAt (payload index : Nat) : InitialLine :=
  let word := payload >>> (208*index)
  ⟨Int.ofNat (word % 1099511627776),
   Int.ofNat ((word >>> 40) % 1099511627776),
   Int.ofNat ((word >>> 80) % 18446744073709551616),
   Int.ofNat ((word >>> 144) % 18446744073709551616)⟩

def initialLineGuard (line : InitialLine) : Bool :=
  decide (0 < line.intercept ∧ 0 < line.slope) &&
    tangentGuard line.n line.d line.intercept q line.slope q

end Compact3684.Elementary
