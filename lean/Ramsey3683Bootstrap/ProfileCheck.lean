import Ramsey3683Bootstrap.ReflectedProfile
import Kernel.ProfileGuard

set_option autoImplicit false
namespace Compact3684.ProfileCheck
open Ramsey3683Bootstrap Set
open Log18 (q scale q_pos_real value)
open Certificate (scalar scale_pos)

noncomputable def Line.realLine (line : Line) : AffineLine := ⟨value line.a,value line.b⟩
noncomputable def cut (lines : Nat → Line) (i : Nat) : ℝ :=
  (deltaA lines i : ℝ)/(deltaB lines i : ℝ)
noncomputable def profile (lines : Nat → Line) (n : Nat) : ℝ → ℝ :=
  affineProfile (fun i : Fin (n+1) => (lines i.val).realLine)

theorem shapeGuard_sound {lines : Nat → Line} {n : Nat}
    (h : ∀ i, i ≤ n → shapeGuard lines n i = true) :
    OrderedLines n (fun i => (lines i).realLine) (cut lines) := by
  have hg (i : Nat) (hi : i ≤ n) := of_decide_eq_true (h i hi)
  have hdb (i : Nat) (hi : i < n) : (0 : ℝ) < (deltaB lines i : ℝ) := by
    have hh := (hg i hi.le).2.2.1 hi
    exact_mod_cast (show 0 < deltaB lines i by dsimp [deltaB]; omega)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have hs := (hg i hi.le).2.2.1 hi
    exact (div_le_div_iff_of_pos_right q_pos_real).mpr (by exact_mod_cast hs.2.le)
  · intro i hi
    have hd := hdb i hi
    simp only [Line.realLine,AffineLine.eval,cut,value]
    have hd' : (lines i).b - (lines (i+1)).b ≠ 0 := by
      have := (hg i hi.le).2.2.1 hi
      omega
    simp only [deltaA,deltaB,Int.cast_sub] at hd ⊢
    field_simp [q_pos_real.ne',hd.ne']
    <;> ring
  · intro i hi
    have hc := (hg i (by omega)).2.2.2 hi
    exact (div_le_div_iff₀ (hdb i (by omega)) (hdb (i+1) hi)).mpr
      (by exact_mod_cast hc.le)

theorem activeGuard_sound {lines : Nat → Line} {n i : Nat} {num den : Int}
    (hshape : ∀ j, j ≤ n → shapeGuard lines n j = true)
    (hactive : activeGuard lines n i num den = true) :
    profile lines n ((num : ℝ)/den) = (lines i).realLine.eval ((num : ℝ)/den) := by
  have hg := of_decide_eq_true hactive
  rcases hg with ⟨hd,hi,hl,hr⟩
  have hdR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hdb (j : Nat) (hj : j < n) : (0 : ℝ) < (deltaB lines j : ℝ) := by
    have hh := (of_decide_eq_true (hshape j hj.le)).2.2.1 hj
    exact_mod_cast (show 0 < deltaB lines j by dsimp [deltaB]; omega)
  apply (shapeGuard_sound hshape).profile_at hi
  · intro hi0
    exact (div_le_div_iff₀ (hdb (i-1) (by omega)) hdR).mpr (by exact_mod_cast hl hi0)
  · intro hin
    exact (div_le_div_iff₀ hdR (hdb i hin)).mpr (by exact_mod_cast hr hin)

private theorem weighted_value (w a b : Int) :
    scalar w * value a + (1-scalar w)*value b =
      ((w*a+(scale-w)*b : Int) : ℝ)/((scale : ℝ)*(q : ℝ)) := by
  simp only [scalar,value,Int.cast_add,Int.cast_sub,Int.cast_mul]
  field_simp [scale_pos.ne',q_pos_real.ne']
  <;> ring

theorem supportGuard_sound {lines : Nat → Line} {n i j : Nat} {w a b : Int}
    (h : supportGuard lines n i j w a b = true) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    profile lines n r ≤ value a+value b*r := by
  have hg := of_decide_eq_true h
  rcases hg with ⟨hi,hj,hw,hwS,hzero,hone⟩
  have hwR : scalar w ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by exact_mod_cast hw) scale_pos.le,?_⟩
    exact (div_le_one scale_pos).mpr (by exact_mod_cast hwS)
  apply affineProfile_support_unit (fun k : Fin (n+1) => (lines k.val).realLine)
    ⟨i,by omega⟩ ⟨j,by omega⟩ hwR ?_ ?_ hr
  · change scalar w*value (lines i).a+(1-scalar w)*value (lines j).a ≤ value a
    rw [weighted_value]
    apply (div_le_iff₀ (mul_pos scale_pos q_pos_real)).mpr
    have hh : ((w*(lines i).a+(scale-w)*(lines j).a : Int) : ℝ) ≤ ((scale*a : Int) : ℝ) := by
      exact_mod_cast hzero
    calc
      _ ≤ ((scale*a : Int) : ℝ) := hh
      _ = _ := by simp only [value,Int.cast_mul]; field_simp [q_pos_real.ne'] <;> ring
  · change scalar w*(value (lines i).a+value (lines i).b)+
      (1-scalar w)*(value (lines j).a+value (lines j).b) ≤ value a+value b
    have hadd (x y : Int) : value x+value y=value (x+y) := by simp [value,add_div]
    rw [hadd,hadd,hadd,weighted_value]
    apply (div_le_iff₀ (mul_pos scale_pos q_pos_real)).mpr
    have hh : ((w*((lines i).a+(lines i).b)+(scale-w)*((lines j).a+(lines j).b) : Int) : ℝ) ≤
        ((scale*(a+b) : Int) : ℝ) := by exact_mod_cast hone
    calc
      _ ≤ ((scale*(a+b) : Int) : ℝ) := hh
      _ = _ := by simp only [value,Int.cast_mul]; field_simp [q_pos_real.ne'] <;> ring

theorem regionGuard_sound {lines : Nat → Line} {n : Nat} {w : RegionWitness}
    (hF : RamseyLean.UniformRamseyExpBound (profile lines n))
    (h : regionGuard lines n w = true) :
    (Real.exp (-scalar w.a),Real.exp (-scalar w.b)) ∈ RamseyLean.asymptoticRegionInterior := by
  have hh := Bool.and_eq_true_iff.mp h
  have hp := Bool.and_eq_true_iff.mp hh.1
  have hpos : 50 < w.a ∧ 50 < w.b := of_decide_eq_true hp.1
  have ha : scalar 50 < scalar w.a :=
    (div_lt_div_iff_of_pos_right scale_pos).mpr (by exact_mod_cast hpos.1)
  have hb : scalar 50 < scalar w.b :=
    (div_lt_div_iff_of_pos_right scale_pos).mpr (by exact_mod_cast hpos.2)
  have he (z : Int) : value ((z-50)*1000000) = scalar z-scalar 50 := by
    simp only [value,scalar,Int.cast_mul,Int.cast_sub]
    norm_num [q,scale]
    ring
  apply region_of_strict_support hF (Certificate.scalar_pos (by norm_num : (0 : Int) < 50)) ha hb
  · intro r hr
    have hs := supportGuard_sound hp.2 (show r ∈ Icc (0 : ℝ) 1 from ⟨hr.1.le,hr.2⟩)
    rw [he,he] at hs
    simpa only [mul_comm] using hs
  · intro r hr
    have hs := supportGuard_sound hh.2 (show r ∈ Icc (0 : ℝ) 1 from ⟨hr.1.le,hr.2⟩)
    rw [he,he] at hs
    simpa only [mul_comm] using hs

#print axioms shapeGuard_sound
#print axioms activeGuard_sound
#print axioms supportGuard_sound
#print axioms regionGuard_sound
end Compact3684.ProfileCheck
