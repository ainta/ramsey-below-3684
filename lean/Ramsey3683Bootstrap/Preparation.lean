import Ramsey3683Bootstrap.WeightedMoment
import Ramsey3683Bootstrap.FiniteContinuation
import Mathlib.Tactic

/-! Quantitative one-shot preparation and exact integer threshold rounding. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Prepare the fixed right set once. The loss is a constant factor, not a
factor paid on every continuation step. -/
theorem exists_prepared_candidate {X Y : Finset V} {p p₀ : ℝ}
    (hcan : Candidate G X Y) (hpp : p < p₀) (hp1 : p < 1)
    (hd : p₀ ≤ redDensity G X Y) :
    ∃ X' : Finset V, X' ⊆ X ∧ Candidate G X' Y ∧ RowFloor G X' Y p ∧
      ((p₀ - p) / (1 - p)) * (#X : ℝ) ≤ (#X' : ℝ) := by
  classical
  let X' := redRegularCore G p X Y
  have hne : X'.Nonempty := redRegularCore_nonempty
    hcan.left_nonempty hcan.right_nonempty (hpp.le.trans hd)
  have hsub : X' ⊆ X := redRegularCore_subset p X Y
  refine ⟨X', hsub, hcan.subcandidate hsub Finset.Subset.rfl hne hcan.right_nonempty, ?_, ?_⟩
  · intro v hv
    exact (mem_redRegularCore_iff.mp hv).2
  · have h := redRegularCore_retains_fraction hcan hpp.le hd
    rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.mpr hp1)]
    simpa only [mul_comm] using h

/-- The extra one gives an exact lower bound after deleting the blue pivot. -/
noncomputable def ceilThreshold (w : ℝ) : ℕ := ⌈w⌉₊ + 1

theorem ceilThreshold_pos (w : ℝ) : 0 < ceilThreshold w := by
  unfold ceilThreshold
  omega

/-- A real threshold gap of two absorbs both ceiling and pivot errors. -/
theorem ceilThreshold_step {previous current q : ℝ}
    (hp : 0 ≤ previous) (hq : q ≤ 1)
    (hgap : previous + 2 ≤ (1 - q) * current) :
    (ceilThreshold previous : ℝ) ≤ (1 - q) * ((ceilThreshold current : ℝ) - 1) := by
  have hprev := Nat.ceil_lt_add_one hp
  have hcur := Nat.le_ceil current
  have ht : (ceilThreshold previous : ℝ) ≤ previous + 2 := by
    simp only [ceilThreshold, Nat.cast_add, Nat.cast_one]
    linarith
  have hid : (ceilThreshold current : ℝ) - 1 = (⌈current⌉₊ : ℝ) := by
    simp [ceilThreshold]
  rw [hid]
  exact ht.trans (hgap.trans (mul_le_mul_of_nonneg_left hcur (sub_nonneg.mpr hq)))

end Ramsey3683Bootstrap
