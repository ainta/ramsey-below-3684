import Std

/-! Executable exact arithmetic for a bounded KERNEL COMPUTATION benchmark.
This file does NOT prove that its intervals enclose the real logarithm.
Such a soundness theorem is required before using it in a Ramsey proof. -/
set_option autoImplicit false
namespace Compact3684.Bench

def q : Int := 10^40
def scale : Int := 10^12
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
  | some (nn,dd,k) => some (plus (reduced nn dd) (timesInt (reduced 2 1) k))

def blueGuard (cost density : Int) : Bool :=
  if cost ≤ 0 ∨ density ≤ 0 ∨ density ≥ scale then false else
  match logarithm (scale-density) scale with
  | none => false
  | some l => decide (0 < (rat cost scale).1 + l.1)

end Compact3684.Bench

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.Bench
def inputs : List (Int × Int) := [(2718466512375,934024143703),
(2726756185074,934568801325),
(2735143742999,935115314139),
(2743631268148,935663694059),
(2760016515284,936709270929),
(2768709268122,937257057262),
(2777508442102,937806721493),
(2786416306442,938358270574),
(2795435201660,938911711413),
(2804567612307,939467055080),
(2813816053843,940024309646),
(2823183110479,940583482348),
(2832671530623,941144585036),
(2842283999216,941707620452),
(2852023502456,942272603482),
(2861892957327,942839539145),
(2879834786593,943855956920),
(2889972555478,944422256898),
(2900249887522,944990522692),
(2910670215906,945560763306),
(2921237088292,946132987145),
(2931954230945,946707205126),
(2942825419874,947283423408),
(2953854694157,947861654399),
(2965046153097,948441905572),
(2976404057944,949024184513),
(2987932909802,949608502413),
(2999637381910,950194870040),
(3011522235978,950783293158),
(3023592557734,951373783775),
(3035853557449,951966349654),
(3056390782579,952942766786),
(3069048722935,953534660462),
(3081914510247,954128644414),
(3094994363494,954724728176),
(3108294732200,955322919091),
(3121822441627,955923228108),
(3135584582351,956525663939),
(3149588644759,957130238132),
(3163842470547,957736961914),
(3178354136949,958345840424),
(3193132346972,958956888131),
(3208186057892,959570112050),
(3231749056736,960511625463),
(3247381673073,961124132064),
(3263319798509,961738828959),
(3279574558256,962355727754),
(3296157652019,962974838682),
(3313081361667,963596169329),
(3330358874296,964219734639),
(3348003970736,964845543414),
(3366031238133,965473604092),
(3384456212920,966103927396),
(3411666823166,967013824657),
(3430936546142,967643374024),
(3450656788056,968275204127),
(3470847323918,968909321635),
(3491529455473,969545739222),
(3512725815268,970184465449),
(3542985653903,971073164964),
(3565283948853,971711045814),
(3588174897068,972351251397),
(3611688670657,972993793916),
(3644540884688,973866592414)]
theorem checked_blue_sample : inputs.all (fun p => blueGuard p.1 p.2) = true := by decide
#print axioms checked_blue_sample
end Compact3684.Bench
