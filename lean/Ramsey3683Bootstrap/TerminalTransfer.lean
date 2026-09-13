import Ramsey3683Bootstrap.TerminalCore
import RamseyLean.Asymptotics.Uniform
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean Filter Topology
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem internal_half_or_compl (Z : Finset V) :
    InternalRedAtLeast G Z (1 / 2) ∨ InternalRedAtLeast Gᶜ Z (1 / 2) := by
  classical
  have hrow (v : V) (hv : v ∈ Z) :
      (#(G.neighborFinset v ∩ Z) : ℝ) + (#(Gᶜ.neighborFinset v ∩ Z) : ℝ) =
      (#Z : ℝ) - 1 := by
    have hd : Disjoint (G.neighborFinset v ∩ Z) (Gᶜ.neighborFinset v ∩ Z) := by
      apply Finset.disjoint_left.mpr
      intro w hwR hwB
      have hr : G.Adj v w := (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwR).1
      have hb : Gᶜ.Adj v w := (Gᶜ.mem_neighborFinset v w).mp (Finset.mem_inter.mp hwB).1
      simpa [SimpleGraph.compl_adj, hr] using hb
    have hu : (G.neighborFinset v ∩ Z) ∪ (Gᶜ.neighborFinset v ∩ Z) = Z.erase v := by
      ext w
      by_cases hw : w = v
      · subst w; simp
      · by_cases hr : G.Adj v w <;> simp [hw, Ne.symm hw, hr]
    have hc := Finset.card_union_of_disjoint hd
    rw [hu, Finset.card_erase_of_mem hv] at hc
    have hn : 1 ≤ #Z := Finset.card_pos.mpr ⟨v, hv⟩
    exact_mod_cast hc.symm
  have he : (∑ v ∈ Z, (#(G.neighborFinset v ∩ Z) : ℝ)) +
      (∑ v ∈ Z, (#(Gᶜ.neighborFinset v ∩ Z) : ℝ)) =
      (#Z : ℝ) * ((#Z : ℝ) - 1) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _v ∈ Z, ((#Z : ℝ) - 1) := Finset.sum_congr rfl hrow
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  unfold InternalRedAtLeast
  by_cases h : (1 / 2 : ℝ) * ((#Z : ℝ) * ((#Z : ℝ) - 1)) ≤
      ∑ v ∈ Z, (#(G.neighborFinset v ∩ Z) : ℝ)
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem finite_terminal_dense {Z : Finset V} {k : ℕ} {C B s : ℝ}
    (hk : 2 ≤ k) (hlarge : 32 * (k : ℝ) ^ 3 ≤ (#Z : ℝ))
    (hdense : InternalRedAtLeast G Z (1 / 2))
    (hnoRed : ¬ hasRedClique G Z k) (hnoBlue : ¬ hasBlueClique G Z k)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (hD : 1 ≤ (B + s ^ 2 - 1) / s)
    (hR : ∀ r : ℕ, 0 < r → r ≤ k → (ramseyNumber r k : ℝ) ≤ C * B ^ r) :
    (#Z : ℝ) ≤ 8 * (k : ℝ) * C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ k := by
  obtain ⟨W, S, hWZ, hS, hSk, hXbig, hsize, havg⟩ :=
    exists_terminal_core G hk hlarge hdense hnoRed
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hX : (W \ S).Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < #(W \ S) := (by positivity : (0 : ℝ) < 4 * (k : ℝ) ^ 2).trans_le hXbig
    exact_mod_cast this
  have ht := MaximumRedClique.all_spines_transfer G hS Finset.sdiff_subset hX
    (fun hb => hnoBlue (hasBlueClique_mono hWZ hb)) hs havg
    (fun r hr hrS => hR r hr (by omega))
  have hs0 : 0 < s := by linarith
  have hp : 0 < s ^ #S := pow_pos hs0 _
  have hdiv : (#(W \ S) : ℝ) ≤
      C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ #S := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ hp).mpr ht
  have hpow : ((B + s ^ 2 - 1) / s) ^ #S ≤ ((B + s ^ 2 - 1) / s) ^ k :=
    pow_le_pow_right₀ hD hSk.le
  have hbound := hdiv.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    _ ≤ 8 * (k : ℝ) * (#(W \ S) : ℝ) := hsize
    _ ≤ 8 * (k : ℝ) * (C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ k) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem finite_terminal {Z : Finset V} {k : ℕ} {C B s : ℝ}
    (hk : 2 ≤ k) (hnoRed : ¬ hasRedClique G Z k) (hnoBlue : ¬ hasBlueClique G Z k)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (hD : 1 ≤ (B + s ^ 2 - 1) / s)
    (hR : ∀ r : ℕ, 0 < r → r ≤ k → (ramseyNumber r k : ℝ) ≤ C * B ^ r) :
    (#Z : ℝ) ≤ max (32 * (k : ℝ) ^ 3)
      (8 * (k : ℝ) * C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ k) := by
  classical
  by_cases hn : 32 * (k : ℝ) ^ 3 ≤ (#Z : ℝ)
  · apply le_max_of_le_right
    rcases internal_half_or_compl G Z with hd | hd
    · exact finite_terminal_dense G hk hn hd hnoRed hnoBlue hC hB hs hD hR
    · exact finite_terminal_dense Gᶜ hk hn hd hnoBlue
        (by simpa only [hasBlueClique, compl_compl, hasRedClique] using hnoRed)
        hC hB hs hD hR
  · exact le_max_of_le_left (le_of_not_ge hn)

/-- An actual finite diagonal Ramsey bound, conditional only on the stated
off-diagonal Ramsey inequalities. No terminal-transfer oracle is assumed. -/
theorem ramsey_terminal {k : ℕ} {C B s : ℝ} (hk : 2 ≤ k)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hs : 1 ≤ s)
    (hD : 1 ≤ (B + s ^ 2 - 1) / s)
    (hR : ∀ r : ℕ, 0 < r → r ≤ k → (ramseyNumber r k : ℝ) ≤ C * B ^ r) :
    (ramseyNumber k k : ℝ) ≤ max (32 * (k : ℝ) ^ 3)
      (8 * (k : ℝ) * C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ k) + 2 := by
  let v : ℝ := max (32 * (k : ℝ) ^ 3)
    (8 * (k : ℝ) * C * B * s ^ 2 * ((B + s ^ 2 - 1) / s) ^ k)
  have hv : 0 ≤ v := le_max_of_le_left (by positivity)
  have hb : RamseyBound k k (ceilThreshold v) := by
    intro G
    classical
    by_contra hn
    have hno := not_or.mp hn
    have h := finite_terminal G hk hno.1 hno.2 hC hB hs hD hR
    have hceil : v < (ceilThreshold v : ℝ) := by
      have := Nat.le_ceil v
      simp only [ceilThreshold, Nat.cast_add, Nat.cast_one]
      linarith
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact (not_le_of_gt hceil) h
  have h := ramseyNumber_le hb
  have hr : (ramseyNumber k k : ℝ) ≤ ceilThreshold v := by exact_mod_cast h
  apply hr.trans
  have hc := Nat.ceil_lt_add_one hv
  simp only [ceilThreshold, Nat.cast_add, Nat.cast_one]
  change _ ≤ v + 2
  linarith

theorem eventually_polynomial_le_exp (c : ℝ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ n ≤ Real.exp (δ * (k : ℝ)) := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt n
    (Real.one_lt_exp_iff.mpr hδ)).const_mul (|c| + 1)
  have ht' : Tendsto (fun k : ℕ => (|c| + 1) * ((k : ℝ) ^ n / (Real.exp δ) ^ k))
      atTop (𝓝 (0 : ℝ)) := by simpa using ht
  filter_upwards [ht'.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with k hk
  have hp : 0 < (Real.exp δ) ^ k := pow_pos (Real.exp_pos δ) k
  rw [← mul_div_assoc, div_lt_one hp] at hk
  have hc : c ≤ |c| + 1 := by linarith [le_abs_self c]
  have h := (mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ n)).trans hk.le
  simpa only [← Real.exp_nat_mul, mul_comm (k : ℝ) δ] using h

/-- Uniform affine Ramsey bounds imply the all-spines diagonal exponent.
All finite-size corrections are explicit in `ramsey_terminal` and are
absorbed here by fixed positive exponential slack. -/
theorem terminal_exp_of_uniform {a b s : ℝ}
    (hF : UniformRamseyExpBound (fun r => a + b * r)) (ha : 0 ≤ a) (hs : 1 ≤ s)
    (hD : 1 ≤ (Real.exp b + s ^ 2 - 1) / s) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (ramseyNumber k k : ℝ) ≤
        Real.exp ((a + Real.log ((Real.exp b + s ^ 2 - 1) / s) + ε) * (k : ℝ)) := by
  intro ε hε
  let D := (Real.exp b + s ^ 2 - 1) / s
  have hε4 : 0 < ε / 4 := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  filter_upwards [hF.eventually (ε / 4) hε4, eventually_ge_atTop 2,
    eventually_polynomial_le_exp (8 * Real.exp b * s ^ 2) 1 hε4,
    eventually_polynomial_le_exp 32 3 hε2,
    eventually_polynomial_le_exp 3 0 hε2] with k hFk hk hlinear hcubic hthree
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR : ∀ r : ℕ, 0 < r → r ≤ k →
      (ramseyNumber r k : ℝ) ≤ Real.exp ((a + ε / 4) * (k : ℝ)) * (Real.exp b) ^ r := by
    intro r hr hrk
    rw [ramseyNumber_comm r k]
    apply (hFk r hr hrk).trans_eq
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    field_simp
    <;> ring
  have hfinite := ramsey_terminal hk (Real.exp_pos ((a + ε / 4) * (k : ℝ))).le
    (Real.exp_pos b).le hs hD hR
  let v := (a + Real.log D + ε / 2) * (k : ℝ)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcubic' : 32 * (k : ℝ) ^ 3 ≤ Real.exp v := hcubic.trans
    (Real.exp_le_exp.mpr (by dsimp [v]; nlinarith))
  have hlinear' : 8 * (k : ℝ) * Real.exp ((a + ε / 4) * (k : ℝ)) * Real.exp b * s ^ 2 * D ^ k ≤
      Real.exp v := by
    have he : D ^ k = Real.exp ((k : ℝ) * Real.log D) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < D)]
    rw [he]
    have h := mul_le_mul_of_nonneg_right hlinear
      (mul_nonneg (Real.exp_pos ((a + ε / 4) * (k : ℝ))).le
        (Real.exp_pos ((k : ℝ) * Real.log D)).le)
    simp only [pow_one] at h
    calc
      _ ≤ Real.exp ((ε / 4) * (k : ℝ)) *
          (Real.exp ((a + ε / 4) * (k : ℝ)) * Real.exp ((k : ℝ) * Real.log D)) := by
        nlinarith only [h]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [v]; ring
  have hmax : max (32 * (k : ℝ) ^ 3)
      (8 * (k : ℝ) * Real.exp ((a + ε / 4) * (k : ℝ)) * Real.exp b * s ^ 2 * D ^ k) ≤
      Real.exp v := max_le hcubic' hlinear'
  have heone : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
  have hthree' : 3 ≤ Real.exp ((ε / 2) * (k : ℝ)) := by simpa using hthree
  calc
    _ ≤ Real.exp v + 2 := hfinite.trans (by change _ + 2 ≤ _ + 2; linarith [hmax])
    _ ≤ Real.exp v * Real.exp ((ε / 2) * (k : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hthree' (Real.exp_pos v).le]
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [v, D]; ring

theorem diagonal_lt_base_of_uniform {a b c : ℝ}
    (hF : UniformRamseyExpBound (fun r => a + b * r)) (ha : 0 ≤ a)
    (hb : 2 < Real.exp b)
    (hc : 2 * Real.exp a * Real.sqrt (Real.exp b - 1) < c) :
    ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ c ^ k := by
  let s := Real.sqrt (Real.exp b - 1)
  have hsnonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = Real.exp b - 1 := Real.sq_sqrt (by linarith)
  have hs : 1 ≤ s := by nlinarith
  have hs0 : 0 < s := by linarith
  have hD : (Real.exp b + s ^ 2 - 1) / s = 2 * s := by
    apply (div_eq_iff hs0.ne').mpr
    nlinarith
  have hD1 : 1 ≤ (Real.exp b + s ^ 2 - 1) / s := by rw [hD]; linarith
  have hc0 : 0 < c := (by positivity : (0 : ℝ) < 2 * Real.exp a * s).trans hc
  have hgap : 0 < Real.log c - (a + Real.log (2 * s)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mp
    rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * s), Real.exp_log hc0]
    nlinarith only [hc]
  have h := terminal_exp_of_uniform hF ha hs hD1
    (Real.log c - (a + Real.log (2 * s))) hgap
  filter_upwards [h] with k hk
  rw [hD] at hk
  have he : (a + Real.log (2 * s) + (Real.log c - (a + Real.log (2 * s)))) * (k : ℝ) =
      (k : ℝ) * Real.log c := by ring
  rw [he, Real.exp_nat_mul, Real.exp_log hc0] at hk
  exact hk

#print axioms ramsey_terminal
#print axioms terminal_exp_of_uniform
#print axioms diagonal_lt_base_of_uniform
end Ramsey3683Bootstrap
