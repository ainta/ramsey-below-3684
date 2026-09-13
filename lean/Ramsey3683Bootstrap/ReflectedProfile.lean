import Ramsey3683Bootstrap.Certificate

/-! Constant-size profile queries. Adjacent line geometry is certified once,
then one active-line index suffices at each cover endpoint. -/
set_option autoImplicit false
namespace Ramsey3683Bootstrap
open Set

theorem affineProfile_support_unit {ι : Type} [Fintype ι] [Nonempty ι]
    (lines : ι → AffineLine) (i j : ι) {weight a b : ℝ}
    (hw : weight ∈ Icc (0 : ℝ) 1)
    (hzero : weight*(lines i).intercept+(1-weight)*(lines j).intercept ≤ a)
    (hone : weight*((lines i).intercept+(lines i).slope)+
      (1-weight)*((lines j).intercept+(lines j).slope) ≤ a+b)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : affineProfile lines r ≤ a+b*r := by
  have hleft := mul_le_mul_of_nonneg_left (affineProfile_le lines i r) hw.1
  have hright := mul_le_mul_of_nonneg_left (affineProfile_le lines j r) (sub_nonneg.mpr hw.2)
  have h0 := mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr hr.2)
  have h1 := mul_le_mul_of_nonneg_left hone hr.1
  dsimp [AffineLine.eval] at hleft hright
  nlinarith only [hleft,hright,h0,h1]

theorem affineProfile_concave {ι : Type} [Fintype ι] [Nonempty ι]
    (lines : ι → AffineLine) : ConcaveOn ℝ univ (affineProfile lines) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [smul_eq_mul]
  apply Finset.le_inf'
  intro i hi
  calc
    _ ≤ α * (lines i).eval x + β * (lines i).eval y :=
      add_le_add (mul_le_mul_of_nonneg_left (affineProfile_le lines i x) hα)
        (mul_le_mul_of_nonneg_left (affineProfile_le lines i y) hβ)
    _ = _ := by
      have he : β = 1-α := by linarith
      dsimp [AffineLine.eval]
      rw [he]
      ring

theorem affine_le_concave_on_interval {F : ℝ → ℝ} (hF : ConcaveOn ℝ univ F)
    (line : AffineLine) {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r)
    (hl : line.eval l ≤ F l) (hr : line.eval r ≤ F r) : line.eval x ≤ F x := by
  let α := (r-x)/(r-l)
  let β := (x-l)/(r-l)
  have hd : 0 < r-l := sub_pos.mpr hlr
  have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hs : α+β=1 := by dsimp [α,β]; field_simp; ring
  have he : α*l+β*r=x := by dsimp [α,β]; field_simp; ring
  have h := hF.2 (mem_univ l) (mem_univ r) hα hβ hs
  simp only [smul_eq_mul, he] at h
  have heline : α*line.eval l+β*line.eval r=line.eval x := by
    dsimp [AffineLine.eval]
    calc
      _ = (α+β)*line.intercept+line.slope*(α*l+β*r) := by ring
      _ = _ := by rw [hs,he,one_mul]
  rw [← heline]
  exact (add_le_add (mul_le_mul_of_nonneg_left hl hα)
    (mul_le_mul_of_nonneg_left hr hβ)).trans h

private theorem adjacent_le {f : ℕ → ℝ} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → f i ≤ f (i+1)) :
    ∀ j, lo ≤ j → j ≤ hi → f lo ≤ f j := by
  intro j hj
  induction j,hj using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hjhi
    exact (ih (by omega)).trans (h j hj (by omega))

private theorem adjacent_ge {f : ℕ → ℝ} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → f (i+1) ≤ f i) :
    ∀ j, lo ≤ j → j ≤ hi → f j ≤ f lo := by
  intro j hj
  induction j,hj using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hj ih =>
    intro hjhi
    exact (h j hj (by omega)).trans (ih (by omega))

/-- `n` is the final line index. There are n+1 lines and n crossings.
Only adjacent slopes, crossings, and their order are checked. -/
structure OrderedLines (n : ℕ) (lines : ℕ → AffineLine) (cut : ℕ → ℝ) : Prop where
  slope : ∀ i, i < n → (lines (i+1)).slope ≤ (lines i).slope
  meet : ∀ i, i < n → (lines i).eval (cut i) = (lines (i+1)).eval (cut i)
  ordered : ∀ i, i+1 < n → cut i ≤ cut (i+1)

theorem OrderedLines.active_minimum {n : ℕ} {lines : ℕ → AffineLine} {cut : ℕ → ℝ}
    (h : OrderedLines n lines cut) {i : ℕ} (hi : i ≤ n) {x : ℝ}
    (hl : 0 < i → cut (i-1) ≤ x) (hr : i < n → x ≤ cut i) :
    ∀ j, j ≤ n → (lines i).eval x ≤ (lines j).eval x := by
  have hcut {j k : ℕ} (hjk : j ≤ k) (hkn : k < n) : cut j ≤ cut k :=
    adjacent_le (lo := j) (hi := k) (fun t ht htk => h.ordered t (by omega)) k hjk le_rfl
  have hleft (j : ℕ) (hj : j < i) : (lines (j+1)).eval x ≤ (lines j).eval x := by
    have hx : cut j ≤ x := (hcut (by omega : j ≤ i-1) (by omega)).trans (hl (by omega))
    have hs := h.slope j (by omega)
    have hm := h.meet j (by omega)
    have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hx)
    dsimp [AffineLine.eval] at hm ⊢
    nlinarith only [hm,hp]
  have hright (j : ℕ) (hij : i ≤ j) (hjn : j < n) :
      (lines j).eval x ≤ (lines (j+1)).eval x := by
    have hx : x ≤ cut j := (hr (by omega)).trans (hcut hij hjn)
    have hs := h.slope j hjn
    have hm := h.meet j hjn
    have hp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hx)
    dsimp [AffineLine.eval] at hm ⊢
    nlinarith only [hm,hp]
  intro j hj
  by_cases hji : j ≤ i
  · exact adjacent_ge (f := fun j => (lines j).eval x) (lo := j) (hi := i)
      (fun t ht hti => hleft t hti) i hji le_rfl
  · exact adjacent_le (f := fun j => (lines j).eval x) (lo := i) (hi := j)
      (fun t hit htj => hright t hit (by omega)) j (by omega) le_rfl

theorem OrderedLines.profile_at {n : ℕ} {lines : ℕ → AffineLine} {cut : ℕ → ℝ}
    (h : OrderedLines n lines cut) {i : ℕ} (hi : i ≤ n) {x : ℝ}
    (hl : 0 < i → cut (i-1) ≤ x) (hr : i < n → x ≤ cut i) :
    affineProfile (fun j : Fin (n+1) => lines j.val) x = (lines i).eval x := by
  apply le_antisymm
  · exact affineProfile_le (fun j : Fin (n+1) => lines j.val) ⟨i,by omega⟩ x
  · apply Finset.le_inf'
    intro j hj
    exact h.active_minimum hi hl hr j.val (by omega)

#print axioms affineProfile_support_unit
#print axioms OrderedLines.profile_at
#print axioms affine_le_concave_on_interval
end Ramsey3683Bootstrap
