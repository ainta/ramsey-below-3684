import RamseyLean.BookInduction

/-!
Weighted degree regularization and child transport.

The graph operation is the upstream `redRegularCore`, not a new oracle.
The key identity is
  excess^r * |X|^(theta-r) * |Y|^(1-r)
    = (density-q)^r * |X|^theta * |Y|.
Thus the same excess-monotone pruning works whenever theta <= r.

-/
set_option autoImplicit false
namespace Ramsey3683Bootstrap

open RamseyLean
open scoped Finset
universe u

noncomputable def weightedMoment (q θ : ℝ) (r : ℕ)
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℝ :=
  (redDensity G X Y - q) ^ r * (#X : ℝ) ^ θ * (#Y : ℝ)

noncomputable def weightedExcessMoment (q θ : ℝ) (r : ℕ)
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) : ℝ :=
  (excess G q X Y) ^ r * (#X : ℝ) ^ (θ - (r : ℝ)) *
    (#Y : ℝ) ^ (1 - (r : ℝ))

private theorem pow_mul_rpow_sub {x θ : ℝ} (hx : 0 < x) (r : ℕ) :
    x ^ r * x ^ (θ - (r : ℝ)) = x ^ θ := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hx]
  congr 1
  ring

private theorem rpow_antitone_base {a b s : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : s ≤ 0) : b ^ s ≤ a ^ s := by
  have hb : 0 < b := ha.trans_le hab
  have hi : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb ha).2 hab
  have h := Real.rpow_le_rpow (inv_nonneg.mpr hb.le) hi (neg_nonneg.mpr hs)
  simpa only [← Real.rpow_neg_eq_inv_rpow, neg_neg] using h

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem weightedExcessMoment_eq_weightedMoment
    {X Y : Finset V} (hX : X.Nonempty) (hY : Y.Nonempty)
    (q θ : ℝ) (r : ℕ) :
    weightedExcessMoment q θ r G X Y = weightedMoment q θ r G X Y := by
  have hNX : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  have hNY : (0 : ℝ) < #Y := by exact_mod_cast hY.card_pos
  have hx := pow_mul_rpow_sub (θ := θ) hNX r
  have hy := pow_mul_rpow_sub (θ := 1) hNY r
  rw [Real.rpow_one] at hy
  unfold weightedExcessMoment weightedMoment
  rw [excess_eq_density_sub_mul (G := G) (p := q) hX hY]
  simp only [mul_pow]
  calc
    ((redDensity G X Y - q) ^ r * ((#X : ℝ) ^ r * (#Y : ℝ) ^ r)) *
        (#X : ℝ) ^ (θ - (r : ℝ)) * (#Y : ℝ) ^ (1 - (r : ℝ)) =
        (redDensity G X Y - q) ^ r *
          ((#X : ℝ) ^ r * (#X : ℝ) ^ (θ - (r : ℝ))) *
          ((#Y : ℝ) ^ r * (#Y : ℝ) ^ (1 - (r : ℝ))) := by ring
    _ = (redDensity G X Y - q) ^ r * (#X : ℝ) ^ θ * (#Y : ℝ) := by
      rw [hx, hy]

/-- Unlike arbitrary subsampling, threshold pruning does not lose weighted
potential. There is no assumption that |X| stays approximately constant. -/
theorem weightedMoment_le_redRegularCore
    {X Y : Finset V} {q θ : ℝ} {r : ℕ}
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hd : q ≤ redDensity G X Y) (hθr : θ ≤ (r : ℝ)) :
    weightedMoment q θ r G X Y ≤
      weightedMoment q θ r G (redRegularCore G q X Y) Y := by
  classical
  let C := redRegularCore G q X Y
  have hC : C.Nonempty := redRegularCore_nonempty hX hY hd
  have hCX : C ⊆ X := redRegularCore_subset q X Y
  have hNC : (0 : ℝ) < #C := by exact_mod_cast hC.card_pos
  have hCard : (#C : ℝ) ≤ (#X : ℝ) := by
    exact_mod_cast Finset.card_le_card hCX
  have hEx : 0 ≤ excess G q X Y := by
    rw [excess_eq_density_sub_mul (G := G) (p := q) hX hY]
    exact mul_nonneg (sub_nonneg.mpr hd) (by positivity)
  have hE : excess G q X Y ≤ excess G q C Y :=
    excess_le_redRegularCore (H := G) (q := q) (A := X) (B := Y)
  have hpow := pow_le_pow_left₀ hEx hE r
  have hsize : (#X : ℝ) ^ (θ - (r : ℝ)) ≤ (#C : ℝ) ^ (θ - (r : ℝ)) :=
    rpow_antitone_base hNC hCard (sub_nonpos.mpr hθr)
  rw [← weightedExcessMoment_eq_weightedMoment hX hY q θ r,
      ← weightedExcessMoment_eq_weightedMoment hC hY q θ r]
  unfold weightedExcessMoment
  have hprod := mul_le_mul hpow hsize
    (Real.rpow_nonneg (Nat.cast_nonneg #X) _) (pow_nonneg (hEx.trans hE) r)
  exact mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (Nat.cast_nonneg #Y) _)

/-- Weighted analogue of upstream `exists_redDegreeRegularized`, using its
same graph core and its same hereditary-density theorem. -/
theorem exists_weightedRegularized
    {X Y : Finset V} {q θ : ℝ} {r : ℕ}
    (h : Candidate G X Y) (hd : q ≤ redDensity G X Y)
    (hθr : θ ≤ (r : ℝ)) :
    ∃ C : Finset V, C ⊆ X ∧ Candidate G C Y ∧
      (∀ ⦃T : Finset V⦄, T.Nonempty → T ⊆ C → q ≤ redDensity G T Y) ∧
      weightedMoment q θ r G X Y ≤ weightedMoment q θ r G C Y := by
  classical
  let C := redRegularCore G q X Y
  have hC : C.Nonempty := redRegularCore_nonempty h.left_nonempty h.right_nonempty hd
  have hCX : C ⊆ X := redRegularCore_subset q X Y
  refine ⟨C, hCX, h.subcandidate hCX Finset.Subset.rfl hC h.right_nonempty, ?_, ?_⟩
  · intro T hT hTC
    exact redDensity_ge_of_subset_redRegularCore hT h.right_nonempty hTC
  · exact weightedMoment_le_redRegularCore h.left_nonempty h.right_nonempty hd hθr

/-- The fixed-factor cost of preparing a hereditary degree floor. Stated
without division so the denominator's sign is not silently assumed. -/
theorem redRegularCore_retains_fraction
    {X Y : Finset V} {q p : ℝ}
    (h : Candidate G X Y) (hqp : q ≤ p) (hd : p ≤ redDensity G X Y) :
    (p - q) * (#X : ℝ) ≤ (1 - q) * (#(redRegularCore G q X Y) : ℝ) := by
  let C := redRegularCore G q X Y
  have hC : C.Nonempty := redRegularCore_nonempty
    h.left_nonempty h.right_nonempty (hqp.trans hd)
  have hE := excess_le_redRegularCore (H := G) (q := q) (A := X) (B := Y)
  rw [excess_eq_density_sub_mul (G := G) (p := q) h.left_nonempty h.right_nonempty,
      excess_eq_density_sub_mul (G := G) (p := q) hC h.right_nonempty] at hE
  have hlo : (p - q) * ((#X : ℝ) * (#Y : ℝ)) ≤
      (redDensity G X Y - q) * ((#X : ℝ) * (#Y : ℝ)) :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hd q) (by positivity)
  have hhi : (redDensity G C Y - q) * ((#C : ℝ) * (#Y : ℝ)) ≤
      (1 - q) * ((#C : ℝ) * (#Y : ℝ)) :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right (redDensity_le_one C Y) q)
      (by positivity)
  have hYpos : (0 : ℝ) < #Y := by exact_mod_cast h.right_card_pos
  apply le_of_mul_le_mul_right _ hYpos
  simpa [C, mul_assoc] using hlo.trans (hE.trans hhi)

/-- Scalar transport once a red/blue child has been chosen. The right-side
cardinality has exponent one, while the left cardinality has exponent theta. -/
theorem weightedMoment_child_ge
    {X Y C Y' : Finset V} {qParent qChild θ z ρ : ℝ} {r : ℕ}
    (hz : 0 ≤ z)
    (hparent : 0 ≤ redDensity G X Y - qParent)
    (hselected : redDensity G X Y - qParent ≤ redDensity G X Y' - qChild)
    (hchild : 0 ≤ redDensity G C Y' - qChild)
    (hside : z * (redDensity G X Y' - qChild) ^ r * (#X : ℝ) ^ θ ≤
      ρ * (redDensity G C Y' - qChild) ^ r * (#C : ℝ) ^ θ)
    (hright : ρ * (#Y : ℝ) ≤ (#Y' : ℝ)) :
    z * weightedMoment qParent θ r G X Y ≤ weightedMoment qChild θ r G C Y' := by
  have hpow := pow_le_pow_left₀ hparent hselected r
  have hfirst : z * (redDensity G X Y - qParent) ^ r * (#X : ℝ) ^ θ ≤
      z * (redDensity G X Y' - qChild) ^ r * (#X : ℝ) ^ θ := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hz)
      (Real.rpow_nonneg (Nat.cast_nonneg #X) θ)
  unfold weightedMoment
  calc
    z * ((redDensity G X Y - qParent) ^ r * (#X : ℝ) ^ θ * (#Y : ℝ)) =
        (z * (redDensity G X Y - qParent) ^ r * (#X : ℝ) ^ θ) * (#Y : ℝ) := by ring
    _ ≤ (ρ * (redDensity G C Y' - qChild) ^ r * (#C : ℝ) ^ θ) * (#Y : ℝ) :=
      mul_le_mul_of_nonneg_right (hfirst.trans hside) (Nat.cast_nonneg #Y)
    _ = ((redDensity G C Y' - qChild) ^ r * (#C : ℝ) ^ θ) * (ρ * (#Y : ℝ)) := by ring
    _ ≤ ((redDensity G C Y' - qChild) ^ r * (#C : ℝ) ^ θ) * (#Y' : ℝ) :=
      mul_le_mul_of_nonneg_left hright
        (mul_nonneg (pow_nonneg hchild r) (Real.rpow_nonneg (Nat.cast_nonneg #C) θ))

end Ramsey3683Bootstrap
