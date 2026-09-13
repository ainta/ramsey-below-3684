import RamseyLean.BlueBook
import Mathlib.Tactic

/-!
Finite maximum-clique book extraction.

The resulting page has BOTH a cardinality lower bound and an improved red
clique bound. The asymptotic entropy/core argument needed to obtain the
fixed-beta transfer theorem is not yet supplied by this file.
-/

set_option autoImplicit false

namespace Ramsey3683Bootstrap

open RamseyLean
open scoped Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A common red neighbourhood restricted to a specified reservoir. -/
def commonRedNeighbors (A X : Finset V) : Finset V :=
  X.filter (fun v => A ⊆ G.neighborFinset v)

/-- Maximum means maximum CARDINALITY, not merely inclusion maximality. -/
structure MaximumRedClique (W S : Finset V) : Prop where
  subset : S ⊆ W
  clique : G.IsClique (S : Set V)
  maximum : ∀ T : Finset V, T ⊆ W → G.IsClique (T : Set V) → #T ≤ #S

theorem exists_maximumRedClique (W : Finset V) :
    ∃ S : Finset V, MaximumRedClique G W S := by
  classical
  let C := W.powerset.filter (fun S : Finset V => G.IsClique (S : Set V))
  have hC : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C]
  obtain ⟨S, hSC, hmax⟩ := Finset.exists_max_image C Finset.card hC
  have hS := Finset.mem_filter.mp hSC
  refine ⟨S, ⟨Finset.mem_powerset.mp hS.1, hS.2, ?_⟩⟩
  intro T hTW hT
  apply hmax T
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTW, hT⟩

/-- The crucial use of a maximum clique: a red clique in a page joins its
spine, so their orders add to at most the maximum clique order. -/
theorem MaximumRedClique.page_card_bound {W S A X T : Finset V}
    (hS : MaximumRedClique G W S) (hAS : A ⊆ S) (hXW : X ⊆ W)
    (hTP : T ⊆ commonRedNeighbors G A X)
    (hT : G.IsClique (T : Set V)) : #A + #T ≤ #S := by
  classical
  have hTX : T ⊆ X := hTP.trans (Finset.filter_subset _ _)
  have hcross : G.IsCompleteBetween (A : Set V) (T : Set V) := by
    intro a ha t ht
    have hp := Finset.mem_filter.mp (hTP ht)
    exact ((G.mem_neighborFinset t a).mp (hp.2 ha)).symm
  have hAT : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvT
    exact G.irrefl (hcross hvA hvT)
  have hAclique : G.IsClique (A : Set V) :=
    hS.clique.subset (Finset.coe_subset.mpr hAS)
  have hUnion : G.IsClique ((A ∪ T : Finset V) : Set V) := by
    rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with haA | haT
    · rcases Finset.mem_union.mp hb with hbA | hbT
      · exact hAclique haA hbA hab
      · exact hcross haA hbT
    · rcases Finset.mem_union.mp hb with hbA | hbT
      · exact (hcross hbA haT).symm
      · exact hT haT hbT hab
  have hbound := hS.maximum (A ∪ T)
    (Finset.union_subset (hAS.trans hS.subset) (hTX.trans hXW)) hUnion
  simpa only [Finset.card_union_of_disjoint hAT] using hbound

/-- A page cannot contain a red clique one larger than the remaining part
of the maximum clique. -/
theorem MaximumRedClique.page_no_red {W S A X : Finset V}
    (hS : MaximumRedClique G W S) (hAS : A ⊆ S) (hXW : X ⊆ W) :
    ¬ hasRedClique G (commonRedNeighbors G A X) (#S - #A + 1) := by
  rintro ⟨T, hTP, hT⟩
  have hcard := MaximumRedClique.page_card_bound G hS hAS hXW hTP hT.isClique
  have hAScard := Finset.card_le_card hAS
  rw [hT.card_eq] at hcard
  omega

end Ramsey3683Bootstrap

