import Kernel.ChainGuard

set_option autoImplicit false
namespace Compact3684.Outer
open Certificate Log18

structure Path where
  start : Nat
  inputLine : Nat
  value : Nat → Int
  ref : Nat → Nat

def initialGuard (d : Chain.Data) (p : Path) : Bool :=
  let line := d.oldLine p.inputLine
  decide (0 < d.N ∧ 0 < p.start ∧ p.start < d.N ∧ p.inputLine ≤ d.oldLast ∧
    0 < p.value p.start ∧
    (line.a*(d.N : Int)+line.b*(p.start : Int))*unit < p.value p.start*q)

def stepGuard (d : Chain.Data) (p : Path) (j : Nat) : Bool :=
  let r := d.node (p.ref j)
  decide (p.ref j < d.nodeCount ∧ r.row = j+1 ∧ 0 < p.value j ∧
    r.value < p.value j ∧ p.value (j+1) = p.value j+r.cost*q)

structure Fraction where
  num : Int
  den : Int

structure Cover where
  kind : Nat
  source : Nat
  row : Nat
  leftActive : Nat
  rightActive : Nat

structure Data where
  chain : Chain.Data
  pathCount : Nat
  path : Nat → Path
  newLast : Nat
  newLine : Nat → ProfileCheck.Line
  coverCount : Nat
  knot : Nat → Fraction
  cover : Nat → Cover

structure ScaledLine where
  a : Int
  b : Int
  den : Int

def sourceLine (d : Data) (c : Cover) : ScaledLine :=
  if c.kind = 0 then
    let line := d.chain.oldLine c.source
    ⟨line.a,line.b,q⟩
  else
    let p := d.path c.source
    let cost := (d.chain.node (p.ref c.row)).cost
    ⟨p.value c.row-cost*(c.row : Int)*q,cost*q*(d.chain.N : Int),valueScale d.chain.N⟩

def endpointGuard (d : Data) (line : ScaledLine) (x : Fraction) (active : Nat) : Bool :=
  ProfileCheck.activeGuard d.newLine d.newLast active x.num x.den &&
    decide ((line.a*x.den+line.b*x.num)*q ≤
      ((d.newLine active).a*x.den+(d.newLine active).b*x.num)*line.den)

def coverGuard (d : Data) (i : Nat) : Bool :=
  let c := d.cover i
  let l := d.knot i
  let r := d.knot (i+1)
  decide (0 < l.den ∧ 0 < r.den ∧ l.num*r.den < r.num*l.den ∧ c.kind ≤ 1 ∧
    (if c.kind = 0 then c.source ≤ d.chain.oldLast else
      c.source < d.pathCount ∧ (d.path c.source).start ≤ c.row ∧ c.row < d.chain.N ∧
      (c.row : Int)*l.den ≤ l.num*(d.chain.N : Int) ∧
      r.num*(d.chain.N : Int) ≤ (c.row+1 : Nat)*r.den)) &&
    endpointGuard d (sourceLine d c) l c.leftActive &&
    endpointGuard d (sourceLine d c) r c.rightActive

def boundaryGuard (d : Data) : Bool :=
  decide (0 < d.coverCount ∧ (d.knot 0).num = 0 ∧
    (d.knot d.coverCount).num = (d.knot d.coverCount).den)

def indexedStepGuard (d : Data) (i : Nat) : Bool :=
  let p := d.path (i/d.chain.N)
  if p.start ≤ i%d.chain.N then stepGuard d.chain p (i%d.chain.N) else true

end Compact3684.Outer
