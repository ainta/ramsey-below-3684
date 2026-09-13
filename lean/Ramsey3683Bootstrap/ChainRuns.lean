import Ramsey3683Bootstrap.ChainColumns

set_option autoImplicit false
namespace Compact3684.Chain
open Ramsey3683Bootstrap Certificate
open Log18 (q)

def Span (d : Data) (r : Run) : Prop :=
  Continuation d.N ((d.node r.lower).row-1) (d.node r.upper).row
    (exponent d.N (runExit d r)) (exponent d.N r.finish)

/-- The arithmetic run guard has real continuation semantics once earlier
density records are interpreted. Its structural checks justify every lookup. -/
theorem runGuard_sound {d : Data} {i : Nat}
    (hcolumns : ∀ j, j < d.nodeCount → columnGuard d j = true)
    (hblocks : ∀ j, j < d.blockCount → blockGuard d j = true)
    (harithmetic : ∀ j, j < d.nodeCount → arithmeticGuard d j = true)
    (hlogs : ∀ j, LogValid (d.log j))
    (h : runGuard d i = true)
    (hprevious : ∀ j, j < d.nodeCount → rank (d.node j) < rank (d.node (d.run i).owner) →
      GridDensity.{0} d.N (d.node j).row (exponent d.N (d.node j).value) (scalar (d.node j).density)) :
    Span d (d.run i) := by
  let run := d.run i
  let upper := d.node run.upper
  let lower := d.node run.lower
  let owner := d.node run.owner
  let b := upper.block
  have hg := of_decide_eq_true h
  rcases hg with ⟨hi,howner,hupper,hlower,hblock,hcol,hlohi,hrank,hpathlo,hpathhi,hmargin,hout,hnext⟩
  have hu := columnGuard_facts (hcolumns _ hupper)
  have hl := columnGuard_facts (hcolumns _ hlower)
  have hb := hblocks _ hu.block_lt
  have hblo : (d.block b).lo ≤ lower.row := by simpa only [b,lower,upper,run,hblock] using hl.lower
  have hbhi : upper.row ≤ (d.block b).hi := hu.upper
  have hlu : lower.row ≤ upper.row := hlohi
  have huLookup : d.lookup upper.row (d.block b).col = run.upper := by
    rw [← hu.column]
    exact hu.lookup_self
  have hlLookup : d.lookup lower.row (d.block b).col = run.lower := by
    have hc : lower.col = (d.block b).col := by simpa only [lower,upper,b,run,hblock] using hl.column
    rw [← hc]
    exact hl.lookup_self
  have heU : rowNode d b upper.row = upper := by simp only [rowNode,huLookup,upper]
  have heL : rowNode d b lower.row = lower := by simp only [rowNode,hlLookup,lower]
  let pref := prefAt d b
  let floor := fun row => (rowNode d b row).value
  let cost := fun row => (rowNode d b row).cost
  let density := fun row => scalar (rowNode d b row).density
  have hrows (row : Nat) (hlo : lower.row ≤ row) (hhi : row ≤ upper.row) :=
    block_rows hcolumns hb row (hblo.trans hlo) (hhi.trans hbhi)
  have hcost (row : Nat) (hlo : lower.row ≤ row) (hhi : row ≤ upper.row) : 0 < cost row :=
    (columnGuard_facts (hcolumns _ (hrows row hlo hhi).index)).cost_pos
  have hblue (row : Nat) (hlo : lower.row ≤ row) (hhi : row ≤ upper.row) :
      0 < scalar (cost row) ∧ density row ∈ Set.Ioo (0 : ℝ) 1 ∧
        0 < scalar (cost row)+Real.log (1-density row) := by
    have ha := Bool.and_eq_true_iff.mp (harithmetic _ (hrows row hlo hhi).index)
    exact blueGuard_sound ha.1 (hlogs _)
  have hd (row : Nat) (hlo : lower.row ≤ row) (hhi : row ≤ upper.row) :
      GridDensity.{0} d.N row (exponent d.N (floor row)) (density row) := by
    have hm := hrows row hlo hhi
    have hcf := columnGuard_facts (hcolumns _ hm.index)
    have hp := hprevious _ hm.index
    have hcolEq : (rowNode d b row).col = upper.col := hm.col_eq.trans hu.column.symm
    have hbound : rank (rowNode d b row) < rank owner := by
      dsimp only [rank]
      rw [hm.row_eq,hcolEq]
      have hcolBound : upper.col < 65536 := hu.col_lt
      change upper.row < owner.row ∨ (upper.row = owner.row ∧ upper.col < owner.col) at hrank
      omega
    have hprev := hp hbound
    change GridDensity d.N (rowNode d b row).row (exponent d.N (floor row)) (density row) at hprev
    rw [hm.row_eq] at hprev
    exact hprev
  have hmonotone := fun row hlo hhi => block_adjusted_step hcolumns hb (row := row) hlo hhi
  have hbeforeL : pref (lower.row-1) = before lower := by
    dsimp only [pref]
    rw [block_before hcolumns hb hblo (hlu.trans hbhi),heL]
  have hprefU : pref upper.row = upper.pref := by
    simp only [pref,prefAt,if_neg (not_lt.mpr (hblo.trans hlu)),heU]
  have hbeforeU : pref (upper.row-1) = before upper := by
    dsimp only [pref]
    rw [block_before hcolumns hb (hblo.trans hlu) hbhi,heU]
  have hmaximum : RangeBound floor pref lower.row upper.row (runMaximum d run) := by
    by_cases hdir : (d.block b).increasing = true
    · have hm := range_bound_of_increasing (value := floor) (pref := pref)
        (blockLo := (d.block b).lo) (blockHi := (d.block b).hi)
        (fun row hlo hhi => by
          have hh := hmonotone row hlo hhi
          change (if (d.block b).increasing = true then _ else _) at hh
          rw [if_pos hdir] at hh
          simpa only [Nat.add_sub_cancel] using hh)
        hblo hbhi
      have heMax : runMaximum d run = upper.value-before upper := by
        change (if (d.block b).increasing = true then upper else lower).value-
          before (if (d.block b).increasing = true then upper else lower) = _
        rw [if_pos hdir]
      rw [heMax]
      simpa only [floor,heU,hbeforeU] using hm
    · have hm := range_bound_of_decreasing (value := floor) (pref := pref)
        (blockLo := (d.block b).lo) (blockHi := (d.block b).hi)
        (fun row hlo hhi => by
          have hh := hmonotone row hlo hhi
          change (if (d.block b).increasing = true then _ else _) at hh
          rw [if_neg hdir] at hh
          simpa only [Nat.add_sub_cancel] using hh)
        hblo hbhi
      have heMax : runMaximum d run = lower.value-before lower := by
        change (if (d.block b).increasing = true then upper else lower).value-
          before (if (d.block b).increasing = true then upper else lower) = _
        rw [if_neg hdir]
      rw [heMax]
      simpa only [floor,heL,hbeforeL] using hm
  have hcont := continuation_of_range hu.grid hl.row_pos hlu pref floor cost density
    (x := run.finish) (maximum := runMaximum d run)
    (fun row hlo hhi => block_prefix_step hcolumns hb (hblo.trans hlo) (hhi.trans hbhi))
    hcost (fun row hlo hhi => (hblue row hlo hhi).2.1.2)
    (fun row hlo hhi => (hblue row hlo hhi).2.2) hmaximum
    (by simpa only [hprefU] using hmargin)
    (by rw [hprefU,hbeforeL]; change 0 < run.finish-(upper.pref-before lower) at hout; omega) hd
  have he : run.finish-pref upper.row+pref (lower.row-1) = runExit d run := by
    rw [hprefU,hbeforeL]
    dsimp only [runExit,runCost,upper,lower]
    omega
  rw [he] at hcont
  exact hcont

#print axioms runGuard_sound
end Compact3684.Chain
