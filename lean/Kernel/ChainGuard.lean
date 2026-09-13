import Kernel.SeedGuard
import Kernel.ProfileGuard

/-! Pure integer structural checker. All tables are untrusted, total data.
Every lookup used by a rule is range-checked and tied to its row/column. -/
set_option autoImplicit false
namespace Compact3684.Chain
open Certificate
open Log18 (q scale CatalogEntry)

structure Node where
  row : Nat
  col : Nat
  start : Nat
  value : Int
  finish : Int
  begin : Int
  cost : Int
  density : Int
  kind : Nat
  baseKind : Nat
  base : Nat
  seed : Seed
  region : Nat
  logBlue : Nat
  logMu : Nat
  logOneMinusMu : Nat
  logPi : Nat
  block : Nat
  pref : Int
  pathStart : Nat
  pathCount : Nat

structure Block where
  lo : Nat
  hi : Nat
  col : Nat
  upper : Nat
  increasing : Bool

structure Run where
  owner : Nat
  upper : Nat
  lower : Nat
  finish : Int

structure Data where
  N : Nat
  nodeCount : Nat
  blockCount : Nat
  runCount : Nat
  regionCount : Nat
  oldLast : Nat
  node : Nat → Node
  block : Nat → Block
  run : Nat → Run
  lookup : Nat → Nat → Nat
  region : Nat → ProfileCheck.RegionWitness
  oldLine : Nat → ProfileCheck.Line
  log : Nat → CatalogEntry

def rank (r : Node) : Nat := r.row*65536+r.col
def before (r : Node) : Int := r.pref-r.cost*q
def runCost (d : Data) (r : Run) : Int := (d.node r.upper).pref-before (d.node r.lower)
def runExit (d : Data) (r : Run) : Int := r.finish-runCost d r
def runMaximum (d : Data) (r : Run) : Int :=
  let hi := d.node r.upper
  let lo := d.node r.lower
  let endpoint := if (d.block hi.block).increasing then hi else lo
  endpoint.value-before endpoint

def blockGuard (d : Data) (i : Nat) : Bool :=
  let b := d.block i
  let r := d.node b.upper
  decide (i < d.blockCount ∧ 0 < b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ d.N ∧ b.col < 65536 ∧
    b.upper < d.nodeCount ∧ r.row = b.hi ∧ r.col = b.col ∧ r.block = i)

def columnGuard (d : Data) (i : Nat) : Bool :=
  let r := d.node i
  let b := d.block r.block
  let prevIndex := d.lookup (r.row-1) r.col
  let prev := d.node prevIndex
  decide (i < d.nodeCount ∧ 0 < d.N ∧ 0 < r.row ∧ r.row ≤ d.N ∧ r.col < 65536 ∧
    0 < r.value ∧ 0 < r.cost ∧ 0 < r.pref ∧ r.block < d.blockCount ∧
    b.lo ≤ r.row ∧ r.row ≤ b.hi ∧ r.col = b.col ∧ d.lookup r.row r.col = i ∧
    (if r.row = b.lo then r.pref = r.cost*q else
      prevIndex < d.nodeCount ∧ prev.row+1 = r.row ∧ prev.col = r.col ∧ prev.block = r.block ∧
      r.pref = prev.pref+r.cost*q ∧
      (if b.increasing then prev.value-before prev ≤ r.value-before r
       else r.value-before r ≤ prev.value-before prev)))

def arithmeticGuard (d : Data) (i : Nat) : Bool :=
  let r := d.node i
  blueGuard r.cost r.density (d.log r.logBlue) &&
    (if r.kind = 1 then
      decide (r.region < d.regionCount ∧ r.seed.a = (d.region r.region).a ∧
        r.seed.b = (d.region r.region).b ∧ r.seed.pi < r.density) &&
      seedGuard r.seed d.N r.start r.row r.begin r.value
        (d.log r.logMu) (d.log r.logOneMinusMu) (d.log r.logPi)
     else true)

def baseGuard (d : Data) (i : Nat) : Bool :=
  let r := d.node i
  if r.kind = 1 then true else
    if r.baseKind = 0 then
      let line := d.oldLine r.base
      decide (r.base ≤ d.oldLast ∧ (line.a*(d.N : Int)+line.b*(r.start : Int))*unit < r.begin*q)
    else
      let parent := d.node r.base
      decide (r.baseKind = 1 ∧ r.base < d.nodeCount ∧ parent.kind = 0 ∧
        parent.row = r.start ∧ parent.value < r.begin ∧ rank parent < rank r)

def pathGuard (d : Data) (i : Nat) : Bool :=
  let r := d.node i
  decide (i < d.nodeCount ∧ r.kind ≤ 1 ∧ 0 < r.start ∧ r.start ≤ r.row ∧
    0 < r.begin ∧ r.begin ≤ r.finish ∧ r.finish < r.value ∧
    r.pathStart+r.pathCount ≤ d.runCount ∧
    (if r.pathCount = 0 then r.start = r.row ∧ r.begin = r.finish else
      let first := d.run r.pathStart
      let last := d.run (r.pathStart+r.pathCount-1)
      first.owner = i ∧ (d.node first.upper).row = r.row ∧ first.finish = r.finish ∧
      last.owner = i ∧ (d.node last.lower).row = r.start+1 ∧ runExit d last = r.begin))

def runGuard (d : Data) (i : Nat) : Bool :=
  let run := d.run i
  let owner := d.node run.owner
  let hi := d.node run.upper
  let lo := d.node run.lower
  let next := d.run (i+1)
  decide (i < d.runCount ∧ run.owner < d.nodeCount ∧ run.upper < d.nodeCount ∧
    run.lower < d.nodeCount ∧ lo.block = hi.block ∧ lo.col = hi.col ∧ lo.row ≤ hi.row ∧
    (hi.row < owner.row ∨ (hi.row = owner.row ∧ hi.col < owner.col)) ∧
    owner.pathStart ≤ i ∧ i < owner.pathStart+owner.pathCount ∧
    hi.pref+runMaximum d run < run.finish ∧ 0 < runExit d run ∧
    (if i+1 < owner.pathStart+owner.pathCount then
      next.owner = run.owner ∧ (d.node next.upper).row+1 = lo.row ∧ next.finish = runExit d run
     else lo.row = owner.start+1 ∧ runExit d run = owner.begin))

end Compact3684.Chain
