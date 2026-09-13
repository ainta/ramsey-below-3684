import Ramsey3683Bootstrap.OuterCover

set_option autoImplicit false
namespace Compact3684.Outer
open Certificate RamseyLean Ramsey3683Bootstrap Set

structure Guards (d : Data) : Prop where
  initial : ∀ p, p < d.pathCount → initialGuard d.chain (d.path p) = true
  steps : ∀ p, p < d.pathCount → ∀ j, (d.path p).start ≤ j → j < d.chain.N →
    stepGuard d.chain (d.path p) j = true
  shapes : ∀ i, i ≤ d.newLast → ProfileCheck.shapeGuard d.newLine d.newLast i = true
  covers : ∀ i, i < d.coverCount → coverGuard d i = true
  boundary : boundaryGuard d = true

abbrev BandIndex (d : Data) := Σ p : Fin d.pathCount, Fin (d.chain.N-(d.path p.val).start)
def bandRow (d : Data) (b : BandIndex d) : Nat := (d.path b.1.val).start+b.2.val
noncomputable def bandStart (d : Data) (b : BandIndex d) : ℝ :=
  exponent d.chain.N ((d.path b.1.val).value (bandRow d b))
noncomputable def bandSlope (d : Data) (b : BandIndex d) : ℝ :=
  scalar (d.chain.node ((d.path b.1.val).ref (bandRow d b))).cost

/-- A complete round, including the outer continuation paths and the finite
cover. Every hypothesis other than the incoming Ramsey theorem is a bounded
Boolean check or the already proved interpretation of its logarithm table. -/
theorem guards_sound {d : Data} (hN : 0 < d.chain.N)
    (hF : UniformRamseyExpBound (ProfileCheck.profile d.chain.oldLine d.chain.oldLast))
    (hlogs : ∀ i, LogValid (d.chain.log i))
    (hchain : Chain.Guards d.chain) (h : Guards d) :
    UniformRamseyExpBound (ProfileCheck.profile d.newLine d.newLast) := by
  have hgood := Chain.guards_sound hF hlogs hchain
  have hbands (b : BandIndex d) : GridBand.{0} d.chain.N (bandRow d b) (bandStart d b) (bandSlope d b) := by
    apply pathGuard_sound hF hlogs hchain.arithmetic hgood (h.initial b.1.val b.1.isLt)
      (h.steps b.1.val b.1.isLt)
    · exact Nat.le_add_right _ _
    · have hi := b.2.isLt
      dsimp [bandRow]
      omega
  have hc := of_decide_eq_true h.boundary
  rcases hc with ⟨hcount,hzero,hone⟩
  have hlastden : 0 < (d.knot d.coverCount).den := by
    have hh := of_decide_eq_true (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (h.covers (d.coverCount-1) (by omega))).1).1
    have he : d.coverCount-1+1=d.coverCount := by omega
    simpa only [he] using hh.2.1
  have hzeroR : (d.knot 0).real = 0 := by simp only [Fraction.real,hzero,Int.cast_zero,zero_div]
  have honeR : (d.knot d.coverCount).real = 1 := by
    simp only [Fraction.real,hone]
    exact div_self (by exact_mod_cast hlastden.ne')
  have hcover (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
      ProfileCheck.profile d.chain.oldLine d.chain.oldLast r ≤ ProfileCheck.profile d.newLine d.newLast r ∨
      ∃ b : BandIndex d, (bandRow d b : ℝ)/d.chain.N ≤ r ∧
        r ≤ ((bandRow d b : ℝ)+1)/d.chain.N ∧
        bandStart d b+bandSlope d b*(r-(bandRow d b : ℝ)/d.chain.N) ≤
          ProfileCheck.profile d.newLine d.newLast r := by
    obtain ⟨i,hi,hri⟩ := interval_cover (fun j => (d.knot j).real) d.coverCount
      (by simpa only [hzeroR] using hr.1) (by simpa only [honeR] using hr.2)
    rcases coverGuard_sound hN h.shapes (h.covers i hi) hri with hold | ⟨p,j,hp,hj,hjn,hl,hu,hline⟩
    · exact Or.inl hold
    · right
      let b : BandIndex d := ⟨⟨p,hp⟩,⟨j-(d.path p).start,by dsimp only; omega⟩⟩
      have hb : bandRow d b = j := by dsimp [bandRow,b]; omega
      refine ⟨b,?_,?_,?_⟩
      · simpa only [hb] using hl
      · simpa only [hb] using hu
      · simpa only [bandStart,bandSlope,hb] using hline
  have hgrid : GridProfile.{0} d.chain.N (ProfileCheck.profile d.newLine d.newLast) := by
    let e := Fintype.equivFin (BandIndex d)
    apply GridProfile.of_cover hN
      (Ramsey3683Bootstrap.UniformRamseyExpBound.gridProfile hF hN)
      (fun i => bandRow d (e.symm i)) (fun i => bandStart d (e.symm i))
      (fun i => bandSlope d (e.symm i)) (fun i => hbands (e.symm i))
    intro r hr
    rcases hcover r hr with hold | ⟨b,hb⟩
    · exact Or.inl hold
    · exact Or.inr ⟨e b,by simpa only [Equiv.symm_apply_apply] using hb⟩
  have hpos (i : Fin (d.newLast+1)) :
      0 ≤ (d.newLine i.val).realLine.intercept ∧ 0 ≤ (d.newLine i.val).realLine.slope := by
    have hs := of_decide_eq_true (h.shapes i.val (by omega))
    exact ⟨(div_pos (by exact_mod_cast hs.1) Log18.q_pos_real).le,
      (div_pos (by exact_mod_cast hs.2.1) Log18.q_pos_real).le⟩
  apply GridProfile.uniform hN _ _ hgrid
  · intro r hr
    exact affineProfile_nonneg (fun i : Fin (d.newLast+1) => (d.newLine i.val).realLine)
      (fun i => (hpos i).1) (fun i => (hpos i).2) hr.1.le
  · intro r hr s hs hrs
    exact affineProfile_monotone (fun i : Fin (d.newLast+1) => (d.newLine i.val).realLine)
      (fun i => (hpos i).2) hrs

#print axioms guards_sound
end Compact3684.Outer
