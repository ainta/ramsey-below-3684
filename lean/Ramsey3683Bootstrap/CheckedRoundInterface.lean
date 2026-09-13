import Ramsey3683Bootstrap.RoundSound
import Kernel.ChainChecks

set_option autoImplicit false
namespace Compact3684

theorem Chain.guards_of_checks {d : Chain.Data}
    (hn : ∀ i, i < d.nodeCount → Chain.nodeGuard d i = true)
    (hb : ∀ i, i < d.blockCount → Chain.blockGuard d i = true)
    (hr : ∀ i, i < d.runCount → Chain.runGuard d i = true)
    (hreg : ∀ i, i < d.regionCount → ProfileCheck.regionGuard d.oldLine d.oldLast (d.region i) = true) :
    Chain.Guards d :=
  ⟨fun i hi => (Chain.nodeGuard_sound (hn i hi)).1,hb,
   fun i hi => (Chain.nodeGuard_sound (hn i hi)).2.1,
   fun i hi => (Chain.nodeGuard_sound (hn i hi)).2.2.1,
   fun i hi => (Chain.nodeGuard_sound (hn i hi)).2.2.2,hr,hreg⟩

theorem Outer.guards_of_checks {d : Outer.Data} (hN : 0 < d.chain.N)
    (hinitial : (List.range d.pathCount).all (fun p => Outer.initialGuard d.chain (d.path p)) = true)
    (hsteps : ∀ i, i < d.pathCount*d.chain.N → Outer.indexedStepGuard d i = true)
    (hshapes : ∀ i, i ≤ d.newLast → ProfileCheck.shapeGuard d.newLine d.newLast i = true)
    (hcovers : ∀ i, i < d.coverCount → Outer.coverGuard d i = true)
    (hboundary : Outer.boundaryGuard d = true) : Outer.Guards d := by
  refine ⟨fun p hp => List.all_eq_true.mp hinitial p (List.mem_range.mpr hp),?_,hshapes,hcovers,hboundary⟩
  intro p hp j hj hjn
  have hi : p*d.chain.N+j < d.pathCount*d.chain.N := by
    calc
      p*d.chain.N+j < p*d.chain.N+d.chain.N := Nat.add_lt_add_left hjn _
      _ = (p+1)*d.chain.N := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ d.pathCount*d.chain.N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp)
  have hg := hsteps (p*d.chain.N+j) hi
  have hdiv : (p*d.chain.N+j)/d.chain.N=p := by
    rw [Nat.mul_comm p, Nat.mul_add_div hN, Nat.div_eq_of_lt hjn, Nat.add_zero]
  have hmod : (p*d.chain.N+j)%d.chain.N=j := Nat.mul_add_mod_of_lt hjn
  simpa only [Outer.indexedStepGuard,hdiv,hmod,if_pos hj] using hg

#print axioms Chain.guards_of_checks
#print axioms Outer.guards_of_checks
end Compact3684
