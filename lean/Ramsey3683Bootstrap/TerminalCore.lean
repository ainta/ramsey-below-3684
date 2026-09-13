import Ramsey3683Bootstrap.AllSpines
import Ramsey3683Bootstrap.GridSemantics

set_option autoImplicit false
namespace Ramsey3683Bootstrap
open RamseyLean
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem MaximumRedClique.external_sum {W S : Finset V} {d : ℝ}
    (hS : MaximumRedClique G W S)
    (hdegree : ∀ v ∈ S, d ≤ (#(G.neighborFinset v ∩ W) : ℝ)) :
    (#S : ℝ) * (d - (#S : ℝ)) ≤
      ∑ v ∈ W \ S, (#(G.neighborFinset v ∩ S) : ℝ) := by
  have hdisj : Disjoint S (W \ S) := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvX
    exact (Finset.mem_sdiff.mp hvX).2 hvS
  have hsplit : S ∪ (W \ S) = W := Finset.union_sdiff_of_subset hS.subset
  have htotal : (#S : ℝ) * d ≤ (redInteredgeCount G S W : ℝ) := by
    calc
      _ = ∑ _v ∈ S, d := by simp
      _ ≤ ∑ v ∈ S, (#(G.neighborFinset v ∩ W) : ℝ) :=
        Finset.sum_le_sum fun v hv => hdegree v hv
      _ = _ := by
        exact_mod_cast (redInteredgeCount_eq_sum_card_neighborFinset_inter
          (G := G) S W).symm
  have hparts : (redInteredgeCount G S W : ℝ) =
      (redInteredgeCount G S S : ℝ) + (redInteredgeCount G S (W \ S) : ℝ) := by
    have h := redInteredgeCount_union_right (G := G) S hdisj
    rw [hsplit] at h
    exact_mod_cast h
  have hinternal : (redInteredgeCount G S S : ℝ) ≤ (#S : ℝ) * (#S : ℝ) := by
    exact_mod_cast redInteredgeCount_le_mul (G := G) S S
  have hsum : (redInteredgeCount G S (W \ S) : ℝ) =
      ∑ v ∈ W \ S, (#(G.neighborFinset v ∩ S) : ℝ) := by
    rw [redInteredgeCount_comm S (W \ S)]
    exact_mod_cast redInteredgeCount_eq_sum_card_neighborFinset_inter
      (G := G) (W \ S) S
  nlinarith

private theorem core_size_algebra {n c k p : ℝ}
    (hk : 1 ≤ k) (hn : 2 * k ≤ n) (hc : 0 ≤ c) (hcn : c ≤ n)
    (hp : 0 ≤ p) (hpdef : 2 * k * p = k - 1)
    (he : (1 / 2 - p) * n ^ 2 - n / 2 ≤ (1 - p) * c ^ 2) :
    n ≤ 4 * k * c := by
  have hkp : 0 < k := by linarith
  have hn0 : 0 < n := by linarith
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * k by positivity)
  have hpn : 2 * k * p * n ^ 2 = (k - 1) * n ^ 2 := congrArg (fun a => a * n ^ 2) hpdef
  have hpc : 2 * k * p * c ^ 2 = (k - 1) * c ^ 2 := congrArg (fun a => a * c ^ 2) hpdef
  have he' : n ^ 2 - k * n ≤ (k + 1) * c ^ 2 := by nlinarith only [hmul, hpn, hpc]
  have hcc : c ^ 2 ≤ c * n := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hcc (show 0 ≤ k + 1 by linarith)
  have hkn : 2 * k * n ≤ n ^ 2 := by nlinarith
  have hkc : (k + 1) * (c * n) ≤ 2 * k * (c * n) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hc hn0.le)
  have hfinal : n * n ≤ (4 * k * c) * n := by nlinarith only [he', hbound, hkn, hkc]
  exact (mul_le_mul_iff_of_pos_right hn0).mp hfinal

private theorem average_floor_algebra {x m k p : ℝ}
    (hk : 1 ≤ k) (hm : 0 ≤ m) (hmk : m ≤ k) (hx : 4 * k ^ 2 ≤ x)
    (hp : 0 ≤ p) (hpp : p ≤ 1 / 2) (hpdef : 2 * k * p = k - 1) :
    (m / 2 - 1) * x ≤ m * (p * (x + m - 1 / 2) - m) := by
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 4 * k ^ 2).trans hx
  have hmp : m / 2 - 1 / 2 ≤ m * p := by
    have h := mul_le_mul_of_nonneg_right hmk (show 0 ≤ 1 / 2 - p by linarith)
    nlinarith
  have hmx := mul_le_mul_of_nonneg_right hmp hx0
  have hmm : m ^ 2 ≤ k ^ 2 := by nlinarith
  have hpmm : 0 ≤ p * m ^ 2 := mul_nonneg hp (sq_nonneg m)
  have hmp' : m * p ≤ k / 2 :=
    (mul_le_mul_of_nonneg_left hpp hm).trans (by linarith)
  have hkk : k ≤ k ^ 2 := by nlinarith
  nlinarith only [hmx, hmm, hpmm, hmp', hx, hkk]

/-- A deliberately loose polynomial threshold keeps the graph argument
linear in cardinalities: using C² ≤ C*N avoids a square-root estimate. -/
theorem exists_terminal_core {Z : Finset V} {k : ℕ}
    (hk : 2 ≤ k) (hlarge : 32 * (k : ℝ) ^ 3 ≤ (#Z : ℝ))
    (hdense : InternalRedAtLeast G Z (1 / 2))
    (hnoRed : ¬ hasRedClique G Z k) :
    ∃ W S : Finset V, W ⊆ Z ∧ MaximumRedClique G W S ∧ #S < k ∧
      4 * (k : ℝ) ^ 2 ≤ (#(W \ S) : ℝ) ∧
      (#Z : ℝ) ≤ 8 * (k : ℝ) * (#(W \ S) : ℝ) ∧
      ((#S : ℝ) / 2 - 1) * (#(W \ S) : ℝ) ≤
        ∑ v ∈ W \ S, (#(G.neighborFinset v ∩ S) : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let p : ℝ := 1 / 2 - 1 / (2 * (k : ℝ))
  have hpdef : 2 * (k : ℝ) * p = (k : ℝ) - 1 := by dsimp [p]; field_simp
  have hp : 0 ≤ p := by nlinarith
  have hpp : p ≤ 1 / 2 := by dsimp [p]; linarith [one_div_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * k)]
  obtain ⟨W, hWZ, hsize, hdegree⟩ := exists_large_degree_core G (p := p) hdense
  obtain ⟨S, hS⟩ := exists_maximumRedClique G W
  have hSk : #S < k := by
    by_contra hn
    exact hnoRed (redClique_lower (le_of_not_gt hn)
      ⟨S, hS.subset.trans hWZ, hS.clique, rfl⟩)
  have hm : (0 : ℝ) ≤ #S := by positivity
  have hmk : (#S : ℝ) ≤ k := by exact_mod_cast hSk.le
  have hWX : (#W : ℝ) = (#(W \ S) : ℝ) + (#S : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hS.subset).symm
  have hkpow : (k : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hn : 2 * (k : ℝ) ≤ (#Z : ℝ) := by nlinarith
  have hWsize := core_size_algebra (by linarith : (1 : ℝ) ≤ k) hn
    (by positivity : (0 : ℝ) ≤ #W) (by exact_mod_cast Finset.card_le_card hWZ)
    hp hpdef (by linarith [hsize])
  have hWbig : 8 * (k : ℝ) ^ 2 ≤ (#W : ℝ) := by
    have h := hlarge.trans hWsize
    have he : 32 * (k : ℝ) ^ 3 = (4 * (k : ℝ)) * (8 * (k : ℝ) ^ 2) := by ring
    rw [he] at h
    exact (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * k)).mp h
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hXbig : 4 * (k : ℝ) ^ 2 ≤ (#(W \ S) : ℝ) := by nlinarith
  have hhalf : (#W : ℝ) ≤ 2 * (#(W \ S) : ℝ) := by nlinarith
  refine ⟨W, S, hWZ, hS, hSk, hXbig, ?_, ?_⟩
  · exact hWsize.trans (by nlinarith [mul_le_mul_of_nonneg_left hhalf hk0.le])
  · have hfloor := average_floor_algebra (by linarith : (1 : ℝ) ≤ k)
      hm hmk hXbig hp hpp hpdef
    rw [← hWX] at hfloor
    exact hfloor.trans (MaximumRedClique.external_sum G hS
      (fun v hv => hdegree v (hS.subset hv)))

#print axioms exists_terminal_core
end Ramsey3683Bootstrap
