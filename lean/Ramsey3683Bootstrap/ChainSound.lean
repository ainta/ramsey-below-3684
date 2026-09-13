import Ramsey3683Bootstrap.ChainPaths
import Ramsey3683Bootstrap.ProfileCheck

set_option autoImplicit false
namespace Compact3684.Chain
open Certificate Ramsey3683Bootstrap RamseyLean

structure Guards (d : Data) : Prop where
  columns : ∀ i, i < d.nodeCount → columnGuard d i = true
  blocks : ∀ i, i < d.blockCount → blockGuard d i = true
  arithmetic : ∀ i, i < d.nodeCount → arithmeticGuard d i = true
  bases : ∀ i, i < d.nodeCount → baseGuard d i = true
  paths : ∀ i, i < d.nodeCount → pathGuard d i = true
  runs : ∀ i, i < d.runCount → runGuard d i = true
  regions : ∀ i, i < d.regionCount → ProfileCheck.regionGuard d.oldLine d.oldLast (d.region i) = true

def Good (d : Data) (i : Nat) : Prop :=
  GridDensity.{0} d.N (d.node i).row (exponent d.N (d.node i).value) (scalar (d.node i).density) ∧
  ((d.node i).kind = 0 → GridUnconditional.{0} d.N (d.node i).row (exponent d.N (d.node i).value))

theorem input_line_bound {line : ProfileCheck.Line} {N row : Nat} {u : Int}
    (hN : 0 < N) (h : (line.a*(N : Int)+line.b*(row : Int))*unit < u*Log18.q) :
    line.realLine.eval ((row : ℝ)/N) < exponent N u := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : line.realLine.eval ((row : ℝ)/N) =
      ((line.a*(N : Int)+line.b*(row : Int) : Int) : ℝ)/((Log18.q : ℝ)*(N : ℝ)) := by
    simp only [ProfileCheck.Line.realLine,AffineLine.eval,Log18.value,
      Int.cast_add,Int.cast_mul,Int.cast_natCast]
    field_simp [hn.ne',Log18.q_pos_real.ne']
    <;> ring
  rw [he]
  apply (div_lt_div_iff₀ (mul_pos Log18.q_pos_real hn) (valueScale_pos hN)).mpr
  have hh : (((line.a*(N : Int)+line.b*(row : Int))*unit : Int) : ℝ) < ((u*Log18.q : Int) : ℝ) := by
    exact_mod_cast h
  have hmul := mul_lt_mul_of_pos_left hh hn
  simp only [valueScale,Int.cast_add,Int.cast_mul,Int.cast_natCast] at hmul ⊢
  nlinarith only [hmul]

/-- Strong induction on the row/column rank interprets every record.
The only numerical premises are the explicit, executable Boolean guards. -/
theorem guards_sound {d : Data}
    (hF : UniformRamseyExpBound (ProfileCheck.profile d.oldLine d.oldLast))
    (hlogs : ∀ i, LogValid (d.log i)) (h : Guards d) :
    ∀ i, i < d.nodeCount → Good d i := by
  have main : ∀ r : Nat, ∀ i, i < d.nodeCount → rank (d.node i) = r → Good d i := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro i hi hr
      have hc := columnGuard_facts (h.columns i hi)
      have hp := of_decide_eq_true (h.paths i hi)
      rcases hp with ⟨_,hkind,hstart,hstartrow,hbegin,hbeginfinish,hfinishvalue,hbounds,hends⟩
      have hprevious (j : Nat) (hj : j < d.nodeCount) (hjrank : rank (d.node j) < rank (d.node i)) : Good d j :=
        ih (rank (d.node j)) (by omega) j hj rfl
      have hcont := pathGuard_sound h.runs (h.paths i hi) (fun j hj => by
        have howner := path_owners h.runs (h.paths i hi) j hj
        apply runGuard_sound h.columns h.blocks h.arithmetic hlogs
          (h.runs ((d.node i).pathStart+j) (by omega))
        intro child hchild hchildrank
        rw [howner] at hchildrank
        exact (hprevious child hchild hchildrank).1)
      have ha := Bool.and_eq_true_iff.mp (h.arithmetic i hi)
      have hblue := blueGuard_sound ha.1 (hlogs (d.node i).logBlue)
      by_cases hk : (d.node i).kind = 1
      · have hs := ha.2
        rw [if_pos hk] at hs
        have hs' := Bool.and_eq_true_iff.mp hs
        have hmatch := of_decide_eq_true hs'.1
        rcases hmatch with ⟨hreg,heA,heB,hpi⟩
        have hregion := ProfileCheck.regionGuard_sound hF (h.regions _ hreg)
        have hregion' : (Real.exp (-scalar (d.node i).seed.a),Real.exp (-scalar (d.node i).seed.b)) ∈
            asymptoticRegionInterior := by simpa only [heA,heB] using hregion
        have hseed := checked_seed_candidate hs'.2 (hlogs _) (hlogs _) (hlogs _) hregion'
        have hseedfacts := seedGuard_sound hs'.2 (hlogs _) (hlogs _) (hlogs _)
        have hpi0 := hseedfacts.2.2.2.2.2.2.1.1
        have hv : 0 < exponent d.N (d.node i).value := exponent_pos hc.grid hc.value_pos
        have hfinished := hcont.1 (d.node i).row (exponent d.N (d.node i).value)
          (scalar (d.node i).seed.pi) hv hseed
        have hd := GridCandidate.density hc.grid hv (exponent_lt hc.grid hfinishvalue).le hpi0.le
          ((div_lt_div_iff_of_pos_right scale_pos).mpr (by exact_mod_cast hpi)) hblue.2.1.2 hfinished
        exact ⟨hd,fun hzero => by omega⟩
      · have hk0 : (d.node i).kind = 0 := by omega
        have hb := h.bases i hi
        change (if (d.node i).kind = 1 then true else _) = true at hb
        rw [if_neg hk] at hb
        have hbase : GridUnconditional.{0} d.N (d.node i).start (exponent d.N (d.node i).begin) := by
          by_cases hinput : (d.node i).baseKind = 0
          · rw [if_pos hinput] at hb
            have hinputfacts := of_decide_eq_true hb
            have hline := input_line_bound hc.grid hinputfacts.2
            have hprofile := GridProfile.row hc.grid hstart (hstartrow.trans hc.row_le)
              (Ramsey3683Bootstrap.UniformRamseyExpBound.gridProfile hF hc.grid)
            apply hprofile.weaken
            have hmin := affineProfile_le (fun j : Fin (d.oldLast+1) => (d.oldLine j.val).realLine)
              ⟨(d.node i).base,by omega⟩ ((d.node i).start/(d.N : ℝ))
            exact hmin.trans hline.le
          · rw [if_neg hinput] at hb
            have hparent := of_decide_eq_true hb
            rcases hparent with ⟨_,hparent,hu,hrow,hvalue,hrank⟩
            have hgood := (hprevious _ hparent hrank).2 hu
            have hweak := hgood.weaken (exponent_lt hc.grid hvalue).le
            simpa only [hrow] using hweak
        have hend := (hcont.2 hbase).weaken (exponent_lt hc.grid hfinishvalue).le
        exact ⟨hend.density _,fun _ => hend⟩
  intro i hi
  exact main (rank (d.node i)) i hi rfl

#print axioms guards_sound
end Compact3684.Chain
