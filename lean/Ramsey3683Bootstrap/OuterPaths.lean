import Ramsey3683Bootstrap.ChainSound
import Kernel.OuterGuard

set_option autoImplicit false
namespace Compact3684.Outer
open Certificate RamseyLean Ramsey3683Bootstrap

theorem pathGuard_sound {d : Chain.Data} {p : Path}
    (hF : UniformRamseyExpBound (ProfileCheck.profile d.oldLine d.oldLast))
    (hlogs : ∀ i, LogValid (d.log i))
    (ha : ∀ i, i < d.nodeCount → Chain.arithmeticGuard d i = true)
    (hg : ∀ i, i < d.nodeCount → Chain.Good d i)
    (hinit : initialGuard d p = true)
    (hsteps : ∀ j, p.start ≤ j → j < d.N → stepGuard d p j = true) :
    ∀ j, p.start ≤ j → j < d.N →
      GridBand.{0} d.N j (exponent d.N (p.value j)) (scalar (d.node (p.ref j)).cost) := by
  have hf := of_decide_eq_true hinit
  rcases hf with ⟨hN,hstart,hstartN,hline,hpos,hinput⟩
  have hbase : GridUnconditional.{0} d.N p.start (exponent d.N (p.value p.start)) := by
    apply (GridProfile.row hN hstart hstartN.le
      (Ramsey3683Bootstrap.UniformRamseyExpBound.gridProfile hF hN)).weaken
    exact (affineProfile_le (fun i : Fin (d.oldLast+1) => (d.oldLine i.val).realLine)
      ⟨p.inputLine,by omega⟩ _).trans (Chain.input_line_bound hN hinput).le
  have hband {j : Nat} (hj : p.start ≤ j) (hjn : j < d.N)
      (hU : GridUnconditional.{0} d.N j (exponent d.N (p.value j))) :
      GridBand.{0} d.N j (exponent d.N (p.value j)) (scalar (d.node (p.ref j)).cost) := by
    have hs := of_decide_eq_true (hsteps j hj hjn)
    rcases hs with ⟨hi,hrow,hpositive,hgap,hstep⟩
    have hb := blueGuard_sound (Bool.and_eq_true_iff.mp (ha _ hi)).1 (hlogs _)
    apply GridUnconditional.band hN (exponent_pos hN hpositive) hb.1 hb.2.1.2 hb.2.2
      (exponent_lt hN hgap) hU
    simpa only [hrow] using (hg _ hi).1
  have hu : ∀ j, p.start ≤ j → j ≤ d.N →
      GridUnconditional.{0} d.N j (exponent d.N (p.value j)) := by
    intro j hj
    induction j,hj using Nat.le_induction with
    | base => intro _; exact hbase
    | succ j hj ih =>
      intro hjn
      have hs := of_decide_eq_true (hsteps j hj (by omega))
      rw [hs.2.2.2.2,Log18.q,exponent_add_cost hN]
      exact (hband hj (by omega) (ih (by omega))).endpoint hN
  intro j hj hjn
  exact hband hj hjn (hu j hj hjn.le)

#print axioms pathGuard_sound
end Compact3684.Outer
