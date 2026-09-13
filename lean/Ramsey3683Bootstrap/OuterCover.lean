import Ramsey3683Bootstrap.OuterPaths

set_option autoImplicit false
namespace Compact3684.Outer
open Certificate RamseyLean Ramsey3683Bootstrap Set

noncomputable def Fraction.real (x : Fraction) : ℝ := (x.num : ℝ)/x.den
noncomputable def ScaledLine.realLine (line : ScaledLine) : AffineLine :=
  ⟨(line.a : ℝ)/line.den,(line.b : ℝ)/line.den⟩

private theorem eval_fraction (a b d n e : Int) (hd : (d : ℝ) ≠ 0) (he : (e : ℝ) ≠ 0) :
    (a : ℝ)/d+((b : ℝ)/d)*((n : ℝ)/e) =
      ((a*e+b*n : Int) : ℝ)/((d : ℝ)*(e : ℝ)) := by
  push_cast
  field_simp
  <;> ring

theorem endpointGuard_sound {d : Data} {line : ScaledLine} {x : Fraction} {active : Nat}
    (hshape : ∀ i, i ≤ d.newLast → ProfileCheck.shapeGuard d.newLine d.newLast i = true)
    (hd : 0 < line.den) (h : endpointGuard d line x active = true) :
    line.realLine.eval x.real ≤ ProfileCheck.profile d.newLine d.newLast x.real := by
  have hh := Bool.and_eq_true_iff.mp h
  have hx := (of_decide_eq_true hh.1).1
  have hdR : (0 : ℝ) < line.den := by exact_mod_cast hd
  have hxR : (0 : ℝ) < x.den := by exact_mod_cast hx
  rw [show x.real = (x.num : ℝ)/x.den from rfl, ProfileCheck.activeGuard_sound hshape hh.1]
  simp only [ScaledLine.realLine,ProfileCheck.Line.realLine,AffineLine.eval,Log18.value]
  rw [eval_fraction _ _ _ _ _ hdR.ne' hxR.ne',
    eval_fraction _ _ _ _ _ Log18.q_pos_real.ne' hxR.ne']
  apply (div_le_div_iff₀ (mul_pos hdR hxR) (mul_pos Log18.q_pos_real hxR)).mpr
  have hhR : (((line.a*x.den+line.b*x.num)*Log18.q : Int) : ℝ) ≤
      ((((d.newLine active).a*x.den+(d.newLine active).b*x.num)*line.den : Int) : ℝ) := by
    exact_mod_cast of_decide_eq_true hh.2
  have hm := mul_le_mul_of_nonneg_right hhR hxR.le
  push_cast at hm ⊢
  nlinarith only [hm]

theorem sourceLine_den_pos {d : Data} (hN : 0 < d.chain.N) (c : Cover) :
    0 < (sourceLine d c).den := by
  dsimp [sourceLine]
  split
  · norm_num [Log18.q]
  · dsimp [valueScale,unit]
    positivity

theorem sourceLine_band {d : Data} {c : Cover} (hN : 0 < d.chain.N) (hc : c.kind ≠ 0) (x : ℝ) :
    (sourceLine d c).realLine.eval x =
      exponent d.chain.N ((d.path c.source).value c.row)+
        scalar (d.chain.node ((d.path c.source).ref c.row)).cost*(x-(c.row : ℝ)/d.chain.N) := by
  have hn : (d.chain.N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [sourceLine,if_neg hc,ScaledLine.realLine,AffineLine.eval,
    exponent,scalar,valueScale,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  norm_num [unit,Log18.q,Log18.scale]
  field_simp
  <;> ring

theorem coverGuard_sound {d : Data} {i : Nat} (hN : 0 < d.chain.N)
    (hshape : ∀ j, j ≤ d.newLast → ProfileCheck.shapeGuard d.newLine d.newLast j = true)
    (h : coverGuard d i = true) {x : ℝ}
    (hx : x ∈ Icc (d.knot i).real (d.knot (i+1)).real) :
    ProfileCheck.profile d.chain.oldLine d.chain.oldLast x ≤ ProfileCheck.profile d.newLine d.newLast x ∨
    ∃ p row, p < d.pathCount ∧ (d.path p).start ≤ row ∧ row < d.chain.N ∧
      (row : ℝ)/d.chain.N ≤ x ∧ x ≤ ((row : ℝ)+1)/d.chain.N ∧
      exponent d.chain.N ((d.path p).value row)+
        scalar (d.chain.node ((d.path p).ref row)).cost*(x-(row : ℝ)/d.chain.N) ≤
          ProfileCheck.profile d.newLine d.newLast x := by
  have hh := Bool.and_eq_true_iff.mp h
  have hg := Bool.and_eq_true_iff.mp hh.1
  have hf := of_decide_eq_true hg.1
  rcases hf with ⟨hl,hr,hlr,hkind,hsource⟩
  have hlR : (0 : ℝ) < (d.knot i).den := by exact_mod_cast hl
  have hrR : (0 : ℝ) < (d.knot (i+1)).den := by exact_mod_cast hr
  have hnR : (0 : ℝ) < d.chain.N := by exact_mod_cast hN
  have hlt : (d.knot i).real < (d.knot (i+1)).real :=
    (div_lt_div_iff₀ hlR hrR).mpr (by exact_mod_cast hlr)
  have hline := affine_le_concave_on_interval
    (affineProfile_concave (fun j : Fin (d.newLast+1) => (d.newLine j.val).realLine))
    (sourceLine d (d.cover i)).realLine hlt hx
    (endpointGuard_sound hshape (sourceLine_den_pos hN _) hg.2)
    (endpointGuard_sound hshape (sourceLine_den_pos hN _) hh.2)
  by_cases hc : (d.cover i).kind = 0
  · rw [if_pos hc] at hsource
    left
    have he : (sourceLine d (d.cover i)).realLine = (d.chain.oldLine (d.cover i).source).realLine := by
      simp only [sourceLine,if_pos hc,ScaledLine.realLine,ProfileCheck.Line.realLine,Log18.value]
    rw [he] at hline
    exact (affineProfile_le (fun j : Fin (d.chain.oldLast+1) => (d.chain.oldLine j.val).realLine)
      ⟨(d.cover i).source,by omega⟩ x).trans hline
  · rw [if_neg hc] at hsource
    rcases hsource with ⟨hp,hstart,hrow,hleft,hright⟩
    right
    refine ⟨(d.cover i).source,(d.cover i).row,hp,hstart,hrow,?_,?_,?_⟩
    · apply le_trans _ hx.1
      exact (div_le_div_iff₀ hnR hlR).mpr (by exact_mod_cast hleft)
    · apply hx.2.trans
      apply (div_le_div_iff₀ hrR hnR).mpr
      exact_mod_cast hright
    · rwa [sourceLine_band hN hc] at hline

theorem interval_cover (f : Nat → ℝ) (n : Nat) {x : ℝ} (hl : f 0 < x) (hr : x ≤ f n) :
    ∃ i, i < n ∧ x ∈ Icc (f i) (f (i+1)) := by
  induction n with
  | zero => exact False.elim (not_lt_of_ge hr hl)
  | succ n ih =>
    by_cases hn : x ≤ f n
    · obtain ⟨i,hi,hx⟩ := ih hn
      exact ⟨i,by omega,hx⟩
    · exact ⟨n,by omega,le_of_lt (lt_of_not_ge hn),hr⟩

#print axioms coverGuard_sound
end Compact3684.Outer
