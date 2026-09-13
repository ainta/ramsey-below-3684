import Kernel.ChainGuard
import Ramsey3683Bootstrap.RunSemantics

set_option autoImplicit false
namespace Compact3684.Chain
open Log18 (q)

structure ColumnFacts (d : Data) (i : Nat) : Prop where
  index : i < d.nodeCount
  grid : 0 < d.N
  row_pos : 0 < (d.node i).row
  row_le : (d.node i).row ≤ d.N
  col_lt : (d.node i).col < 65536
  value_pos : 0 < (d.node i).value
  cost_pos : 0 < (d.node i).cost
  pref_pos : 0 < (d.node i).pref
  block_lt : (d.node i).block < d.blockCount
  lower : (d.block (d.node i).block).lo ≤ (d.node i).row
  upper : (d.node i).row ≤ (d.block (d.node i).block).hi
  column : (d.node i).col = (d.block (d.node i).block).col
  lookup_self : d.lookup (d.node i).row (d.node i).col = i
  following :
    let r := d.node i
    let b := d.block r.block
    let prevIndex := d.lookup (r.row-1) r.col
    let prev := d.node prevIndex
    if r.row = b.lo then r.pref = r.cost*q else
      prevIndex < d.nodeCount ∧ prev.row+1 = r.row ∧ prev.col = r.col ∧ prev.block = r.block ∧
      r.pref = prev.pref+r.cost*q ∧
      (if b.increasing then prev.value-before prev ≤ r.value-before r
       else r.value-before r ≤ prev.value-before prev)

theorem columnGuard_facts {d : Data} {i : Nat} (h : columnGuard d i = true) : ColumnFacts d i := by
  have hg := of_decide_eq_true h
  rcases hg with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩

def rowNode (d : Data) (b row : Nat) : Node := d.node (d.lookup row (d.block b).col)
def prefAt (d : Data) (b row : Nat) : Int :=
  if row < (d.block b).lo then 0 else (rowNode d b row).pref

structure RowMatches (d : Data) (b row : Nat) : Prop where
  index : d.lookup row (d.block b).col < d.nodeCount
  row_eq : (rowNode d b row).row = row
  col_eq : (rowNode d b row).col = (d.block b).col
  block_eq : (rowNode d b row).block = b

/-- The last row plus checked predecessor links certifies that the whole
block is present. Holes or forged row/column aliases cannot pass this proof. -/
theorem block_rows {d : Data} {b : Nat}
    (hcolumns : ∀ i, i < d.nodeCount → columnGuard d i = true)
    (hb : blockGuard d b = true) :
    ∀ row, (d.block b).lo ≤ row → row ≤ (d.block b).hi → RowMatches d b row := by
  have hg := of_decide_eq_true hb
  rcases hg with ⟨hbid,hlo,hlohi,hhi,hcol,hupper,hupperrow,huppercol,hupperblock⟩
  have hlast := columnGuard_facts (hcolumns _ hupper)
  have he : d.lookup (d.block b).hi (d.block b).col = (d.block b).upper := by
    simpa only [hupperrow,huppercol] using hlast.lookup_self
  have hbase : RowMatches d b (d.block b).hi := by
    constructor
    · simpa only [he] using hupper
    · simpa only [rowNode,he] using hupperrow
    · simpa only [rowNode,he] using huppercol
    · simpa only [rowNode,he] using hupperblock
  have hdown (row : Nat) (hrow : (d.block b).lo < row) (hm : RowMatches d b row) :
      RowMatches d b (row-1) := by
    have hf := columnGuard_facts (hcolumns _ hm.index)
    have hs := hf.following
    have heR := hm.row_eq
    have heC := hm.col_eq
    have heB := hm.block_eq
    dsimp only [rowNode] at heR heC heB
    simp only [heR,heC,heB,if_neg (ne_of_gt hrow)] at hs
    refine ⟨hs.1,?_,hs.2.2.1,hs.2.2.2.1⟩
    have hh := hs.2.1
    dsimp [rowNode]
    omega
  have hiter : ∀ t, t ≤ (d.block b).hi-(d.block b).lo → RowMatches d b ((d.block b).hi-t) := by
    intro t
    induction t with
    | zero => intro _; simpa using hbase
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have h := hdown ((d.block b).hi-t) (by omega) hprev
      convert h using 1 <;> omega
  intro row hl hr
  have h := hiter ((d.block b).hi-row) (by omega)
  convert h using 1 <;> omega

theorem block_before {d : Data} {b row : Nat}
    (hcolumns : ∀ i, i < d.nodeCount → columnGuard d i = true)
    (hb : blockGuard d b = true) (hl : (d.block b).lo ≤ row) (hr : row ≤ (d.block b).hi) :
    prefAt d b (row-1) = before (rowNode d b row) := by
  have hm := block_rows hcolumns hb row hl hr
  have hf := columnGuard_facts (hcolumns _ hm.index)
  have hs := hf.following
  have heR := hm.row_eq
  have heC := hm.col_eq
  have heB := hm.block_eq
  dsimp only [rowNode] at heR heC heB
  simp only [heR,heC,heB] at hs
  have hlo : 0 < (d.block b).lo := (of_decide_eq_true hb).2.1
  by_cases he : row = (d.block b).lo
  · rw [if_pos he] at hs
    simp only [prefAt,if_pos (show row-1 < (d.block b).lo by omega),before,rowNode]
    omega
  · rw [if_neg he] at hs
    simp only [prefAt,if_neg (show ¬ row-1 < (d.block b).lo by omega),before,rowNode]
    have hh := hs.2.2.2.2.1
    omega

theorem block_prefix_step {d : Data} {b row : Nat}
    (hcolumns : ∀ i, i < d.nodeCount → columnGuard d i = true)
    (hb : blockGuard d b = true) (hl : (d.block b).lo ≤ row) (hr : row ≤ (d.block b).hi) :
    prefAt d b row = prefAt d b (row-1)+(rowNode d b row).cost*q := by
  rw [block_before hcolumns hb hl hr]
  simp only [prefAt,if_neg (not_lt.mpr hl),before]
  omega

theorem block_adjusted_step {d : Data} {b row : Nat}
    (hcolumns : ∀ i, i < d.nodeCount → columnGuard d i = true)
    (hb : blockGuard d b = true) (hl : (d.block b).lo ≤ row) (hr : row < (d.block b).hi) :
    if (d.block b).increasing then
      (rowNode d b row).value-prefAt d b (row-1) ≤ (rowNode d b (row+1)).value-prefAt d b row
    else
      (rowNode d b (row+1)).value-prefAt d b row ≤ (rowNode d b row).value-prefAt d b (row-1) := by
  have hm := block_rows hcolumns hb (row+1) (by omega) (by omega)
  have hf := columnGuard_facts (hcolumns _ hm.index)
  have hs := hf.following
  have heR := hm.row_eq
  have heC := hm.col_eq
  have heB := hm.block_eq
  dsimp only [rowNode] at heR heC heB
  simp only [heR,heC,heB,if_neg (show row+1 ≠ (d.block b).lo by omega),
    Nat.add_sub_cancel] at hs
  have hbefore := block_before hcolumns hb (row := row+1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hbefore
  rw [hbefore,block_before hcolumns hb hl hr.le]
  exact hs.2.2.2.2.2

#print axioms block_rows
#print axioms block_prefix_step
#print axioms block_adjusted_step
end Compact3684.Chain
