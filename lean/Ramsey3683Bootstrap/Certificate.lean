import Ramsey3683Bootstrap.GridClosure
import Kernel.LogInterval
import Kernel.SeedGuard
import PrefixRange
import Kernel.Elementary
import RamseyLean.Numerics.Core

/-! Certificate soundness connects exact guards directly to the graph rules.
All logarithm facts must come from the checked shared catalog. -/
set_option autoImplicit false
namespace Compact3684.Certificate
open Ramsey3683Bootstrap RamseyLean Set
open Compact3684.Log18 (CatalogEntry Contains value scale q q_pos_real)

noncomputable def scalar (z : Int) : ℝ := (z : ℝ)/(scale : ℝ)
noncomputable def exponent (N : Nat) (z : Int) : ℝ := (z : ℝ)/(valueScale N : ℝ)
def LogValid (e : CatalogEntry) : Prop :=
  Contains (e.lo,e.hi) (Real.log (scalar e.argument))

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
theorem unit_pos : (0 : ℝ) < (unit : ℝ) := by norm_num [unit]
theorem valueScale_pos {N : Nat} (hN : 0 < N) : (0 : ℝ) < (valueScale N : ℝ) := by
  simp only [valueScale, Int.cast_mul, Int.cast_natCast]
  exact mul_pos (by exact_mod_cast hN) unit_pos

theorem scalar_pos {z : Int} (hz : 0 < z) : 0 < scalar z :=
  div_pos (by exact_mod_cast hz) scale_pos
theorem scalar_lt_one {z : Int} (hz : z < scale) : scalar z < 1 :=
  (div_lt_one scale_pos).mpr (by exact_mod_cast hz)

theorem blueGuard_sound {cost p : Int} {logOneMinusP : CatalogEntry}
    (h : blueGuard cost p logOneMinusP = true) (hlog : LogValid logOneMinusP) :
    0 < scalar cost ∧ scalar p ∈ Ioo (0 : ℝ) 1 ∧
      0 < scalar cost + Real.log (1-scalar p) := by
  have hg : 0 < cost ∧ 0 < p ∧ p < scale ∧ logOneMinusP.argument = scale-p ∧
      0 < cost*q+scale*logOneMinusP.lo := of_decide_eq_true h
  refine ⟨scalar_pos hg.1, ⟨scalar_pos hg.2.1,scalar_lt_one hg.2.2.1⟩, ?_⟩
  have hlog' : value logOneMinusP.lo ≤ Real.log (1-scalar p) := by
    have he : scalar logOneMinusP.argument = 1-scalar p := by
      rw [hg.2.2.2.1]
      simp [scalar,Int.cast_sub,scale_pos.ne',sub_div]
    exact he ▸ hlog.1
  have hn : (0 : ℝ) < ((cost*q+scale*logOneMinusP.lo : Int) : ℝ) := by
    exact_mod_cast hg.2.2.2.2
  have hpositive := div_pos hn (mul_pos scale_pos q_pos_real)
  have he : scalar cost + value logOneMinusP.lo =
      ((cost*q+scale*logOneMinusP.lo : Int) : ℝ)/((scale : ℝ)*(q : ℝ)) := by
    simp only [scalar,value,Int.cast_add,Int.cast_mul]
    field_simp [scale_pos.ne', q_pos_real.ne']
    <;> ring
  rw [← he] at hpositive
  linarith

theorem seedGuard_sound {s : Seed} {N i j : Nat} {u v : Int}
    {logMu logOneMinusMu logPi : CatalogEntry}
    (h : seedGuard s N i j u v logMu logOneMinusMu logPi = true)
    (hlogMu : LogValid logMu) (hlogOneMinusMu : LogValid logOneMinusMu) (hlogPi : LogValid logPi) :
    0 < N ∧ 0 < i ∧ i ≤ j ∧ j ≤ N ∧
    0 < scalar s.theta ∧ scalar s.mu ∈ Ioo (0 : ℝ) 1 ∧ scalar s.pi ∈ Ioo (0 : ℝ) 1 ∧
    0 < (1-scalar s.mu)*(scalar s.a+scalar s.theta*Real.log (1-scalar s.mu))+
      Real.log (scalar s.pi) ∧
    scalar s.a+(j : ℝ)/N*scalar s.b-scalar s.theta*((i : ℝ)/N)*Real.log (scalar s.mu) <
      scalar s.theta*exponent N u+exponent N v := by
  have hg := of_decide_eq_true h
  change 0 < N ∧ 0 < i ∧ i ≤ j ∧ j ≤ N ∧
    0 < s.theta ∧ 0 < s.mu ∧ s.mu < scale ∧ 0 < s.pi ∧ s.pi < scale ∧
    logMu.argument = s.mu ∧ logOneMinusMu.argument = scale-s.mu ∧ logPi.argument = s.pi ∧
    0 < densityNumerator s logOneMinusMu.lo logPi.lo ∧
    0 < budgetNumerator s N i j u v logMu.lo at hg
  rcases hg with ⟨hN,hi,hij,hjN,hθ,hμ,hμ1,hπ,hπ1,hargμ,harg1μ,hargπ,hden,hbud⟩
  have hθR := scalar_pos hθ
  have hμR : scalar s.mu ∈ Ioo (0 : ℝ) 1 := ⟨scalar_pos hμ,scalar_lt_one hμ1⟩
  have hπR : scalar s.pi ∈ Ioo (0 : ℝ) 1 := ⟨scalar_pos hπ,scalar_lt_one hπ1⟩
  have hμlo : value logMu.lo ≤ Real.log (scalar s.mu) := hargμ ▸ hlogMu.1
  have hπlo : value logPi.lo ≤ Real.log (scalar s.pi) := hargπ ▸ hlogPi.1
  have h1μlo : value logOneMinusMu.lo ≤ Real.log (1-scalar s.mu) := by
    have he : scalar logOneMinusMu.argument = 1-scalar s.mu := by
      rw [harg1μ]
      simp [scalar,Int.cast_sub,scale_pos.ne',sub_div]
    exact he ▸ hlogOneMinusMu.1
  refine ⟨hN,hi,hij,hjN,hθR,hμR,hπR,?_,?_⟩
  · have hn : (0 : ℝ) < (densityNumerator s logOneMinusMu.lo logPi.lo : ℝ) := by
      exact_mod_cast hden
    have hp := div_pos hn (mul_pos (sq_pos_of_pos scale_pos) q_pos_real)
    have he : (1-scalar s.mu)*(scalar s.a+scalar s.theta*value logOneMinusMu.lo)+value logPi.lo =
        (densityNumerator s logOneMinusMu.lo logPi.lo : ℝ)/((scale : ℝ)^2*(q : ℝ)) := by
      simp only [scalar,value,densityNumerator,Int.cast_add,Int.cast_sub,Int.cast_mul]
      field_simp [scale_pos.ne', q_pos_real.ne']
      <;> ring
    rw [← he] at hp
    exact hp.trans_le (add_le_add
      (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (scalar s.a)) (mul_le_mul_of_nonneg_left h1μlo hθR.le))
        (sub_nonneg.mpr hμR.2.le)) hπlo)
  · have hn : (0 : ℝ) < (budgetNumerator s N i j u v logMu.lo : ℝ) := by exact_mod_cast hbud
    have hp := div_pos hn (mul_pos (mul_pos scale_pos (valueScale_pos hN)) q_pos_real)
    have he : scalar s.theta*exponent N u+exponent N v-scalar s.a-(j : ℝ)/N*scalar s.b+
        scalar s.theta*((i : ℝ)/N)*value logMu.lo =
        (budgetNumerator s N i j u v logMu.lo : ℝ)/
          ((scale : ℝ)*(valueScale N : ℝ)*(q : ℝ)) := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      simp only [scalar,exponent,value,budgetNumerator,valueScale,Int.cast_add,Int.cast_sub,
        Int.cast_mul,Int.cast_natCast]
      field_simp [scale_pos.ne', q_pos_real.ne', unit_pos.ne']
      <;> ring
    rw [← he] at hp
    have hα : 0 ≤ (i : ℝ)/N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hμlo (mul_nonneg hθR.le hα)
    linarith

theorem checked_seed_candidate {s : Seed} {N i j : Nat} {u v : Int}
    {logMu logOneMinusMu logPi : CatalogEntry}
    (h : seedGuard s N i j u v logMu logOneMinusMu logPi = true)
    (hlogMu : LogValid logMu) (hlogOneMinusMu : LogValid logOneMinusMu) (hlogPi : LogValid logPi)
    (hregion : (Real.exp (-scalar s.a),Real.exp (-scalar s.b)) ∈ asymptoticRegionInterior) :
    GridCandidate.{0} N j i (exponent N u) (exponent N v) (scalar s.pi) := by
  obtain ⟨hN,hi,hij,_,hθ,hμ,hπ,hden,hbud⟩ := seedGuard_sound h hlogMu hlogOneMinusMu hlogPi
  exact gridCandidate_of_weighted_seed hN (hi.trans_le hij) hi hθ hμ hπ hregion hden hbud

#print axioms checked_seed_candidate
end Compact3684.Certificate

namespace Compact3684.Elementary
open Compact3684.Log18
open RamseyLean.CertifiedNumerics

theorem timesRat_contains {a : Interval} {x : ℝ} (ha : Contains a x) (n : Int) {d : Int}
    (hd : 0 < d) : Contains (timesRat a n d) ((n : ℝ)/d*x) := by
  have h := (ha.timesInt n).divide hd
  have he : ((n : ℝ)*x)/(d : ℝ) = (n : ℝ)/d*x := by ring
  exact he ▸ h

theorem minus_contains {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (minus a b) (x-y) := by
  have h := ha.plus (hb.timesInt (-1))
  simpa only [Compact3684.Elementary.minus,Int.cast_neg,Int.cast_one,neg_one_mul,sub_eq_add_neg] using h

theorem expSeries_contains {t L : ℝ} {ti : Interval}
    (hti : Contains ti t) (hNti : Nonneg ti)
    (n j : Nat) (w total : Interval)
    (hw : Contains w (t^j/(j.factorial : ℝ))) (hNw : Nonneg w)
    (htotal : Contains total (expPoly j (-t)))
    (hlo : expPoly (j+n) (-t)-value 1 ≤ L) (hhi : L ≤ expPoly (j+n) (-t)+value 1) :
    Contains (expSeries ti n j w total) L := by
  induction n generalizing j w total with
  | zero =>
    simp only [Nat.add_zero] at hlo hhi
    change value (total.1-1) ≤ L ∧ L ≤ value (total.2+1)
    have he : value (total.1-1) = value total.1-value 1 := by simp [value]; ring
    rw [he,value_add]
    constructor <;> linarith [htotal.1,htotal.2]
  | succ n ih =>
    have hd : (0 : Int) < (j : Int)+1 := by omega
    have hnext := (hw.timesPos hti hNw hNti).divide hd
    have he : t^j/(j.factorial : ℝ)*t/(((j : Int)+1 : Int) : ℝ) =
        t^(j+1)/((j+1).factorial : ℝ) := by
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
        Int.cast_add,Int.cast_natCast,Int.cast_one,pow_succ]
      field_simp
      <;> ring
    rw [he] at hnext
    have hadd := htotal.plus (hw.timesInt ((-1 : Int)^j))
    have hterm : (((-1 : Int)^j : Int) : ℝ)*(t^j/(j.factorial : ℝ)) =
        (-t)^j/(j.factorial : ℝ) := by
      calc
        _ = ((-1 : ℝ)*t)^j/(j.factorial : ℝ) := by
          simp only [Int.cast_pow,Int.cast_neg,Int.cast_one,mul_pow]
          ring
        _ = _ := by rw [neg_one_mul]
    rw [hterm] at hadd
    have ht : Contains (plus total (timesInt w ((-1 : Int)^j))) (expPoly (j+1) (-t)) := by
      simpa only [expPoly,Finset.sum_range_succ] using hadd
    apply ih (j+1) (divide (timesPos w ti) (j+1))
      (plus total (timesInt w ((-1 : Int)^j))) hnext ((hNw.timesPos hNti).divide hd) ht
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlo
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hhi

theorem expNeg_contains {n d : Int} (hn : 0 ≤ n) (hd : 0 < d) (hnd : n ≤ d) :
    Contains (expNeg n d) (Real.exp (-((n : ℝ)/d))) := by
  let t : ℝ := (n : ℝ)/d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast hn) hdR.le
  have ht1 : t ≤ 1 := (div_le_one hdR).mpr (by exact_mod_cast hnd)
  have hpoly := exp_taylor_mem (x := -t) (by simpa only [abs_neg,abs_of_nonneg ht0] using ht1)
    (n := 20) (by norm_num)
  have herror : expError 20 (-t) ≤ value 1 := by
    have hp : t^20 ≤ 1 := pow_le_one₀ ht0 ht1
    simp only [expError,abs_neg,abs_of_nonneg ht0]
    calc
      _ ≤ 1 * ((21 : ℝ)/(Nat.factorial 20 * 20)) := by gcongr <;> norm_num
      _ ≤ value 1 := by norm_num [value,q,Nat.factorial]
  apply expSeries_contains (rat_contains hd) (rat_nonneg hn hd) 20 0 (q,q) (0,0)
  · simp [Contains,value,q]
  · exact q_pos.le
  · simp [Contains,expPoly,value_zero]
  · simpa only [Nat.zero_add] using (show expPoly 20 (-t)-value 1 ≤ Real.exp (-t) by linarith [hpoly.1])
  · simpa only [Nat.zero_add] using (show Real.exp (-t) ≤ expPoly 20 (-t)+value 1 by linarith [hpoly.2])

theorem initialValueSlope_domain {n d : Int} {result : Interval × Interval}
    (h : initialValueSlope n d = some result) : 0 < n ∧ 0 < d ∧ n ≤ d := by
  by_cases hbad : n ≤ 0 ∨ d ≤ 0 ∨ d < n
  · simp only [initialValueSlope,if_pos hbad] at h
    contradiction
  · omega

theorem initialValueSlope_contains {n d : Int} {result : Interval × Interval}
    (h : initialValueSlope n d = some result) :
    Contains result.1 (RamseyLean.F RamseyLean.finalB ((n : ℝ)/d)) ∧
    Contains result.2 (RamseyLean.FSlope RamseyLean.finalB ((n : ℝ)/d)) := by
  obtain ⟨hn,hd,hnd⟩ := initialValueSlope_domain h
  have hbad : ¬(n ≤ 0 ∨ d ≤ 0 ∨ d < n) := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htpos : (0 : ℝ) < (n : ℝ)/d := div_pos hnR hdR
  have hd3 : (0 : Int) < 100*d^3 := by positivity
  have hplus : (((d+n : Int) : ℝ)/d) = 1+(n : ℝ)/d := by
    push_cast
    field_simp [hdR.ne']
    <;> ring
  have hpoly : (((-25*n*d^2+3*n^2*d+8*n^3 : Int) : ℝ)/((100*d^3 : Int) : ℝ)) =
      RamseyLean.gPoly RamseyLean.finalB ((n : ℝ)/d) := by
    simp only [RamseyLean.gPoly,RamseyLean.finalB]
    push_cast
    field_simp [hdR.ne']
    <;> ring
  have hdp : (((-25*d^3+31*n*d^2+21*n^2*d-8*n^3 : Int) : ℝ)/((100*d^3 : Int) : ℝ)) =
      -(1/4 : ℝ)+(2*RamseyLean.finalB+1/4)*((n : ℝ)/d)+
        (6/25-RamseyLean.finalB)*((n : ℝ)/d)^2-(2/25)*((n : ℝ)/d)^3 := by
    simp only [RamseyLean.finalB]
    push_cast
    field_simp [hdR.ne']
    <;> ring
  have hratio : (((d+n : Int) : ℝ)/(n : ℝ)) = (1+(n : ℝ)/d)/((n : ℝ)/d) := by
    push_cast
    field_simp [hnR.ne',hdR.ne']
    <;> ring
  have hlogratio : Real.log (((d+n : Int) : ℝ)/(n : ℝ)) =
      Real.log (1+(n : ℝ)/d)-Real.log ((n : ℝ)/d) := by
    rw [hratio,Real.log_div (by positivity) htpos.ne']
  have he := expNeg_contains hn.le hd hnd
  simp only [initialValueSlope,if_neg hbad] at h
  cases hlt : logarithm n d with
  | none => simp only [hlt,Option.bind_none] at h; contradiction
  | some lt =>
    cases hl1t : logarithm (d+n) d with
    | none => simp only [hlt,hl1t,Option.bind_some,Option.bind_none] at h; contradiction
    | some l1t =>
      cases hlratio : logarithm (d+n) n with
      | none => simp only [hlt,hl1t,hlratio,Option.bind_some,Option.bind_none] at h; contradiction
      | some lratio =>
        simp only [hlt,hl1t,hlratio,Option.bind_some,Option.some.injEq] at h
        cases h
        have hv := (minus_contains (timesRat_contains (logarithm_contains hl1t) (d+n) hd)
          (timesRat_contains (logarithm_contains hlt) n hd)).plus
            (timesRat_contains he (-25*n*d^2+3*n^2*d+8*n^3) hd3)
        have hs := (logarithm_contains hlratio).plus
          (timesRat_contains he (-25*d^3+31*n*d^2+21*n^2*d-8*n^3) hd3)
        constructor
        · simpa only [hplus,hpoly,RamseyLean.F,RamseyLean.entropy,RamseyLean.g] using hv
        · rw [hlogratio,hdp] at hs
          simpa only [RamseyLean.FSlope,mul_comm] using hs

theorem tangentGuard_sound {n d an ad bn bd : Int} (h : tangentGuard n d an ad bn bd = true) :
    ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      RamseyLean.F RamseyLean.finalB r ≤ (an : ℝ)/ad+((bn : ℝ)/bd)*r := by
  unfold tangentGuard at h
  split_ifs at h with hbad
  have had : 0 < ad := by omega
  have hbd : 0 < bd := by omega
  cases he : initialValueSlope n d with
  | none => simp only [he,Bool.false_eq_true] at h
  | some result =>
    rcases result with ⟨val,slope⟩
    obtain ⟨hn,hd,hnd⟩ := initialValueSlope_domain he
    obtain ⟨hv,hs⟩ := initialValueSlope_contains he
    have hτpos : (0 : ℝ) < (n : ℝ)/d := div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)
    have hτle : (n : ℝ)/d ≤ 1 := (div_le_one (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
      (by exact_mod_cast hnd)
    simp only [he,decide_eq_true_eq] at h
    have hz := minus_contains hv (timesRat_contains hs n hd)
    have ho := hv.plus (timesRat_contains hs (d-n) hd)
    have ha := rat_contains (n := an) had
    have hab := ha.plus (rat_contains (n := bn) hbd)
    have hzero : RamseyLean.F RamseyLean.finalB ((n : ℝ)/d)-
        ((n : ℝ)/d)*RamseyLean.FSlope RamseyLean.finalB ((n : ℝ)/d) ≤ (an : ℝ)/ad := by
      apply hz.2.trans (le_trans ?_ ha.1)
      exact div_le_div_of_nonneg_right (by exact_mod_cast h.1) q_pos_real.le
    have hone : RamseyLean.F RamseyLean.finalB ((n : ℝ)/d)+
        (1-(n : ℝ)/d)*RamseyLean.FSlope RamseyLean.finalB ((n : ℝ)/d) ≤
          (an : ℝ)/ad+(bn : ℝ)/bd := by
      have hminus : ((d-n : Int) : ℝ)/d = 1-(n : ℝ)/d := by
        push_cast
        field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
        <;> ring
      rw [hminus] at ho
      apply ho.2.trans (le_trans ?_ hab.1)
      exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) q_pos_real.le
    exact Ramsey3683Bootstrap.affine_majorant_of_tangent
      (RamseyLean.strictConcaveOn_F ⟨le_rfl,by norm_num [RamseyLean.finalB,RamseyLean.preliminaryB]⟩).concaveOn
      ⟨hτpos,hτle⟩ (RamseyLean.hasDerivAt_F hτpos) hzero hone

#print axioms tangentGuard_sound

noncomputable def InitialLine.realLine (line : InitialLine) : Ramsey3683Bootstrap.AffineLine :=
  ⟨value line.intercept,value line.slope⟩

theorem initialLineGuard_sound {line : InitialLine} (h : initialLineGuard line = true) :
    0 < line.realLine.intercept ∧ 0 < line.realLine.slope ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1, RamseyLean.F RamseyLean.finalB r ≤ line.realLine.eval r := by
  obtain ⟨hpos,htan⟩ := Bool.and_eq_true_iff.mp h
  have hp : 0 < line.intercept ∧ 0 < line.slope := of_decide_eq_true hpos
  refine ⟨div_pos (by exact_mod_cast hp.1) q_pos_real,
    div_pos (by exact_mod_cast hp.2) q_pos_real, tangentGuard_sound htan⟩

structure InitialChunk where
  count : Nat
  payload : Nat

def InitialChunk.guard (chunk : InitialChunk) : Bool :=
  decide (0 < chunk.count) && (List.range chunk.count).all
    (fun i => initialLineGuard (initialLineAt chunk.payload i))

noncomputable def InitialChunk.line (chunk : InitialChunk) (index : Nat) : Ramsey3683Bootstrap.AffineLine :=
  (initialLineAt chunk.payload (index % chunk.count)).realLine

theorem InitialChunk.sound {chunk : InitialChunk} (h : chunk.guard = true) (index : Nat) :
    0 < (chunk.line index).intercept ∧ 0 < (chunk.line index).slope ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1, RamseyLean.F RamseyLean.finalB r ≤ (chunk.line index).eval r := by
  obtain ⟨hcount,hchecks⟩ := Bool.and_eq_true_iff.mp h
  have hc : 0 < chunk.count := of_decide_eq_true hcount
  exact initialLineGuard_sound (List.all_eq_true.mp hchecks _
    (List.mem_range.mpr (Nat.mod_lt index hc)))

end Compact3684.Elementary
