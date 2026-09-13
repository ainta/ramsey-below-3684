import Ramsey3683Bootstrap.ChainRuns

set_option autoImplicit false
namespace Compact3684.Chain
open Certificate

theorem path_owners {d : Data} {i : Nat}
    (hruns : ∀ j, j < d.runCount → runGuard d j = true)
    (hpath : pathGuard d i = true) :
    ∀ j, j < (d.node i).pathCount → (d.run ((d.node i).pathStart+j)).owner = i := by
  have hp := of_decide_eq_true hpath
  rcases hp with ⟨hi,hkind,hstart,hstartrow,hbegin,hbeginfinish,hfinishvalue,hbounds,hends⟩
  intro j
  induction j with
  | zero =>
    intro hj
    rw [if_neg (by omega : (d.node i).pathCount ≠ 0)] at hends
    simpa only [Nat.add_zero] using hends.1
  | succ j ih =>
    intro hj
    have hprevious := ih (by omega)
    have hr := of_decide_eq_true (hruns ((d.node i).pathStart+j) (by omega))
    rcases hr with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hnext⟩
    rw [hprevious,if_pos (by omega : (d.node i).pathStart+j+1 < (d.node i).pathStart+(d.node i).pathCount)] at hnext
    simpa only [Nat.add_assoc] using hnext.1

/-- Only adjacent run links and the two endpoints are checked. Their
composition is a fixed theorem, rather than an expanded path proof. -/
theorem pathGuard_sound {d : Data} {i : Nat}
    (hruns : ∀ j, j < d.runCount → runGuard d j = true)
    (hpath : pathGuard d i = true)
    (hspans : ∀ j, j < (d.node i).pathCount → Span d (d.run ((d.node i).pathStart+j))) :
    Continuation d.N (d.node i).start (d.node i).row
      (exponent d.N (d.node i).begin) (exponent d.N (d.node i).finish) := by
  have hp := of_decide_eq_true hpath
  rcases hp with ⟨hi,hkind,hstart,hstartrow,hbegin,hbeginfinish,hfinishvalue,hbounds,hends⟩
  by_cases hzero : (d.node i).pathCount = 0
  · rw [if_pos hzero] at hends
    rw [hends.1,hends.2]
    exact Continuation.refl _ _ _
  · rw [if_neg hzero] at hends
    let row := fun j => if j < (d.node i).pathCount then
      (d.node (d.run ((d.node i).pathStart+j)).upper).row else (d.node i).start
    let value := fun j => if j < (d.node i).pathCount then
      exponent d.N (d.run ((d.node i).pathStart+j)).finish else exponent d.N (d.node i).begin
    have hchain : ∀ j, j < (d.node i).pathCount →
        Continuation d.N (row (j+1)) (row j) (value (j+1)) (value j) := by
      intro j hj
      have hspan := hspans j hj
      have howner := path_owners hruns hpath j hj
      have hr := of_decide_eq_true (hruns ((d.node i).pathStart+j) (by omega))
      rcases hr with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hnext⟩
      rw [howner] at hnext
      by_cases hlast : j+1 < (d.node i).pathCount
      · rw [if_pos (by omega : (d.node i).pathStart+j+1 < (d.node i).pathStart+(d.node i).pathCount)] at hnext
        have hrow : (d.node (d.run ((d.node i).pathStart+j)).lower).row-1 =
            (d.node (d.run ((d.node i).pathStart+(j+1))).upper).row := by
          have hh := hnext.2.1
          simp only [Nat.add_assoc] at hh
          omega
        have hvalue : exponent d.N (runExit d (d.run ((d.node i).pathStart+j))) =
            exponent d.N (d.run ((d.node i).pathStart+(j+1))).finish := by
          rw [← hnext.2.2]
          simp only [Nat.add_assoc]
        change Continuation _ _ _ _ _ at hspan
        rw [hrow,hvalue] at hspan
        simpa only [row,value,if_pos hj,if_pos hlast] using hspan
      · rw [if_neg (by omega : ¬ (d.node i).pathStart+j+1 < (d.node i).pathStart+(d.node i).pathCount)] at hnext
        have hrow : (d.node (d.run ((d.node i).pathStart+j)).lower).row-1 = (d.node i).start := by
          have hh := hnext.1
          omega
        change Continuation _ _ _ _ _ at hspan
        rw [hrow,hnext.2] at hspan
        simpa only [row,value,if_pos hj,if_neg hlast] using hspan
    have ht := Continuation.chain d.N (d.node i).pathCount row value hchain
    have hpositive : 0 < (d.node i).pathCount := by omega
    simpa only [row,value,lt_self_iff_false,if_false,if_pos hpositive,Nat.add_zero,
      hends.2.1,hends.2.2.1] using ht

#print axioms path_owners
#print axioms pathGuard_sound
end Compact3684.Chain
