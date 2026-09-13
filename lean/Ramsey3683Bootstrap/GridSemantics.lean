import Ramsey3683Bootstrap.WeightedUniform
import Ramsey3683Bootstrap.Preparation

/-! Grid-aligned semantics. The scale is k=N*m and a grid row j denotes the
blue target j*m. No regularity or robust-target oracle is built into these
definitions. Every eventual cutoff is uniform over the finite graph. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Set Topology
open scoped Finset
universe u

def GridDensity (N j : ℕ) (v p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
      Real.exp ((N * m : ℕ) * (v + ε)) ≤ (#X : ℝ) →
      InternalRedAtLeast G X p →
      hasRedClique G X (N * m) ∨ hasBlueClique G X (j * m)

def GridCandidate (N j i : ℕ) (u v p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj] {X Y : Finset V},
      Candidate G X Y → RowFloor G X Y p →
      Real.exp ((N * m : ℕ) * (u + ε)) ≤ (#X : ℝ) →
      Real.exp ((N * m : ℕ) * (v + ε)) ≤ (#Y : ℝ) →
      Candidate.IsGood G X Y (N * m) (j * m) (i * m)

def GridUnconditional (N i : ℕ) (u : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj] {X : Finset V},
      Real.exp ((N * m : ℕ) * (u + ε)) ≤ (#X : ℝ) →
      hasRedClique G X (N * m) ∨ hasBlueClique G X (i * m)

theorem blueClique_lower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {X : Finset V} {a b : ℕ} (hab : a ≤ b) (hb : hasBlueClique G X b) :
    hasBlueClique G X a := by
  obtain ⟨B, hBX, hB⟩ := hb
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq (hab.trans_eq hB.card_eq.symm)
  exact ⟨A, hAB.trans hBX, hB.isClique.subset (Finset.coe_subset.mpr hAB), hA⟩

theorem redClique_lower {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {X : Finset V} {a b : ℕ} (hab : a ≤ b) (hb : hasRedClique G X b) :
    hasRedClique G X a := by
  obtain ⟨B, hBX, hB⟩ := hb
  obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq (hab.trans_eq hB.card_eq.symm)
  exact ⟨A, hAB.trans hBX, hB.isClique.subset (Finset.coe_subset.mpr hAB), hA⟩

theorem GridUnconditional.density {N i : ℕ} {u : ℝ}
    (h : GridUnconditional.{u} N i u) (p : ℝ) : GridDensity.{u} N i u p := by
  intro ε hε
  filter_upwards [h ε hε] with m hm
  intro V instF instEq G instAdj X hX _
  exact hm hX

/-- The strict slope margin absorbs the ceiling and lost-pivot errors
uniformly over arbitrarily many integer blue steps. -/
theorem eventually_exponential_step {c q h : ℝ}
    (hq : q < 1) (hc : 0 < c + Real.log (1 - q)) (hh : 0 < h) :
    ∀ᶠ m : ℕ in atTop, ∀ a b : ℝ,
      h * (m : ℝ) ≤ a → a + c ≤ b →
      Real.exp a + 2 ≤ (1 - q) * Real.exp b := by
  let gain := (1 - q) * Real.exp c - 1
  have hqpos : 0 < 1 - q := sub_pos.mpr hq
  have hg : 0 < gain := by
    have hx : 1 < Real.exp (c + Real.log (1 - q)) := Real.one_lt_exp_iff.mpr hc
    rw [Real.exp_add, Real.exp_log hqpos] at hx
    dsimp [gain]
    nlinarith
  have ht : Tendsto (fun m : ℕ => gain * Real.exp (h * (m : ℝ))) atTop atTop :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hh)).const_mul_atTop hg
  filter_upwards [ht.eventually_ge_atTop 2] with m hm
  intro a b ha hb
  have hga : 2 ≤ gain * Real.exp a := hm.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) hg.le)
  have hstep : Real.exp a * Real.exp c ≤ Real.exp b := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hb
  have hscaled := mul_le_mul_of_nonneg_left hstep hqpos.le
  dsimp [gain] at hga
  nlinarith

theorem eventually_threshold_step {c q h : ℝ}
    (hq : q < 1) (hc : 0 < c + Real.log (1 - q)) (hh : 0 < h) :
    ∀ᶠ m : ℕ in atTop, ∀ a b : ℝ,
      h * (m : ℝ) ≤ a → a + c ≤ b →
      (ceilThreshold (Real.exp a) : ℝ) ≤
        (1 - q) * ((ceilThreshold (Real.exp b) : ℝ) - 1) := by
  filter_upwards [eventually_exponential_step hq hc hh] with m hm
  intro a b ha hb
  exact ceilThreshold_step (Real.exp_pos a).le hq.le (hm a b ha hb)

/-- Fixed exponential slack pays both ceiling errors uniformly; the
exponent `a` itself is allowed to vary with the graph target. -/
theorem eventually_ceil_exp_padding {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ a : ℝ, 0 ≤ a →
      (ceilThreshold (Real.exp a) : ℝ) ≤ Real.exp (a + δ * (m : ℝ)) := by
  have ht : Tendsto (fun m : ℕ => Real.exp (δ * (m : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hδ)
  filter_upwards [ht.eventually_ge_atTop 3] with m hm
  intro a ha
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos a).le
  have hexp : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have hp := mul_le_mul_of_nonneg_left hm (Real.exp_pos a).le
  rw [Real.exp_add]
  simp only [ceilThreshold, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem exp_le_ceilThreshold (a : ℝ) : Real.exp a ≤ (ceilThreshold (Real.exp a) : ℝ) := by
  have h := Nat.le_ceil (Real.exp a)
  simp only [ceilThreshold, Nat.cast_add, Nat.cast_one]
  linarith

end Ramsey3683Bootstrap
