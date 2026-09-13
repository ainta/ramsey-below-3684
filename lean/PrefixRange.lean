import Std

/-!
The arithmetic bridge for constant-column run compression.

`prefix i` is the accumulated cost up to row i in ONE certificate column.
A range maximum bounds `value i - prefix (i - 1)`. Its single inequality
implies every size inequality in a descending run. These are arithmetic
lemmas, not a Ramsey theorem and not a proof of a particular input file.
-/
set_option autoImplicit false

namespace Compact3684

local notation "ℤ" => Int
local notation "ℕ" => Nat

def RangeBound (value pref : ℕ → ℤ) (lo hi : ℕ) (m : ℤ) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → value i - pref (i - 1) ≤ m

def RangeValid (value pref : ℕ → ℤ) (lo hi : ℕ) (x : ℤ) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → value i < x - (pref hi - pref (i - 1))

/-- A checked range maximum suffices; no path expansion is required here. -/
theorem range_valid_of_bound {value pref : ℕ → ℤ} {lo hi : ℕ} {m x : ℤ}
    (h : RangeBound value pref lo hi m) (hx : pref hi + m < x) :
    RangeValid value pref lo hi x := by
  intro i hlo hhi
  have := h i hlo hhi
  omega

theorem range_bound_singleton (value pref : ℕ → ℤ) (i : ℕ) :
    RangeBound value pref i i (value i - pref (i - 1)) := by
  intro j hlo hhi
  have : j = i := by omega
  subst j
  omega

/-- Local binary-tree checks prove a maximum bound for an entire interval. -/
theorem range_bound_join {value pref : ℕ → ℤ} {lo mid hi : ℕ} {a b : ℤ}
    (hleft : RangeBound value pref lo mid a)
    (hright : RangeBound value pref (mid + 1) hi b) :
    RangeBound value pref lo hi (max a b) := by
  intro i hlo hhi
  by_cases h : i ≤ mid
  · have := hleft i hlo h
    omega
  · have := hright i (by omega) hhi
    omega

/-- A column's adjusted floors are usually monotone on long stretches.
Checking adjacent inequalities once certifies every subrange endpoint
query, without building a segment tree or expanding continuation paths. -/
theorem decreasing_range_le {f : ℕ → ℤ} {lo hi : ℕ}
    (hstep : ∀ i, lo ≤ i → i < hi → f (i+1) ≤ f i) :
    ∀ i, lo ≤ i → i ≤ hi → f i ≤ f lo := by
  intro i
  induction i with
  | zero =>
    intro hli _
    have he : lo = 0 := by omega
    subst lo
    omega
  | succ i ih =>
    intro hli hihi
    by_cases he : lo = i+1
    · subst lo; omega
    · have hs := hstep i (by omega) (by omega)
      have hp := ih (by omega) (by omega)
      omega

theorem increasing_range_le {f : ℕ → ℤ} {lo hi : ℕ}
    (hstep : ∀ i, lo ≤ i → i < hi → f i ≤ f (i+1)) :
    ∀ i, lo ≤ i → i ≤ hi → f lo ≤ f i := by
  intro i
  induction i with
  | zero =>
    intro hli _
    have he : lo = 0 := by omega
    subst lo
    omega
  | succ i ih =>
    intro hli hihi
    by_cases he : lo = i+1
    · subst lo; omega
    · have hs := hstep i (by omega) (by omega)
      have hp := ih (by omega) (by omega)
      omega

theorem range_bound_of_decreasing {value pref : ℕ → ℤ} {blockLo blockHi lo hi : ℕ}
    (hstep : ∀ i, blockLo ≤ i → i < blockHi →
      value (i+1)-pref i ≤ value i-pref (i-1))
    (hl : blockLo ≤ lo) (hh : hi ≤ blockHi) :
    RangeBound value pref lo hi (value lo-pref (lo-1)) := by
  intro i hlo hhi
  apply decreasing_range_le (f := fun i => value i-pref (i-1)) (hi := hi) ?_ i hlo hhi
  intro j hlj hjh
  simpa only [Nat.add_sub_cancel] using hstep j (by omega) (by omega)

theorem range_bound_of_increasing {value pref : ℕ → ℤ} {blockLo blockHi lo hi : ℕ}
    (hstep : ∀ i, blockLo ≤ i → i < blockHi →
      value i-pref (i-1) ≤ value (i+1)-pref i)
    (hl : blockLo ≤ lo) (hh : hi ≤ blockHi) :
    RangeBound value pref lo hi (value hi-pref (hi-1)) := by
  intro i hlo hhi
  apply increasing_range_le (f := fun i => value i-pref (i-1)) (lo := i) (hi := hi) ?_ hi
    hhi (Nat.le_refl hi)
  intro j hij hjh
  simpa only [Nat.add_sub_cancel] using hstep j (by omega) (by omega)

/-- The exit value telescopes when two adjacent descending runs are joined. -/
theorem range_exit_join (pref : ℕ → ℤ) (lo mid hi : ℕ) (x : ℤ) :
    (x - (pref hi - pref mid)) - (pref mid - pref lo) =
      x - (pref hi - pref lo) := by omega

/-- Explicit list semantics for arbitrary sequences of verified summaries. -/
structure Summary where
  cost : ℤ
  need : ℤ
  deriving DecidableEq, Repr

def Summary.thenDo (a b : Summary) : Summary :=
  ⟨a.cost + b.cost, max a.need (a.cost + b.need)⟩

def Valid : List Summary → ℤ → Prop
  | [], x => 0 < x
  | s :: ss, x => s.need < x ∧ Valid ss (x - s.cost)

def summarize : List Summary → Summary
  | [] => ⟨0, 0⟩
  | s :: ss => s.thenDo (summarize ss)

theorem summarize_correct (ss : List Summary) (x : ℤ) :
    (summarize ss).need < x ↔ Valid ss x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change max s.need (s.cost + (summarize ss).need) < x ↔
      s.need < x ∧ Valid ss (x - s.cost)
    rw [← ih]
    omega

/-- No reduction of the expanded list is needed if its summary is supplied
with a proof. This is the interface for separately checked opaque chunks. -/
theorem valid_of_checked_summary {ss : List Summary} {s : Summary} {x : ℤ}
    (hs : summarize ss = s) (hx : s.need < x) : Valid ss x := by
  apply (summarize_correct ss x).mp
  simpa only [hs] using hx

/-- A linear exponent lift along `length` consecutive rows. The summaries
here describe nonempty ranges; the terminal positivity guard stays separate. -/
def linearLift (length row delta : ℤ) (s : Summary) : Summary :=
  ⟨s.cost + length*delta, s.need + (row+1)*delta⟩

/-- Composition preserves the linear lift. In particular, a long path does
NOT lose `length * delta` in its size margin: its need shifts by `(row+1)*delta`.
This is the cancellation used to quantize controls without rebuilding search. -/
theorem linearLift_compose (n m row delta : ℤ) (a b : Summary) :
    (linearLift n row delta a).thenDo (linearLift m (row-n) delta b) =
      linearLift (n+m) row delta (a.thenDo b) := by
  cases a with
  | mk ac an =>
    cases b with
    | mk bc bn =>
      unfold linearLift Summary.thenDo
      congr 1 <;> simp only [Int.add_mul, Int.sub_mul, Int.one_mul] <;> omega

/-- Adding `row * delta` to the owner loses exactly one grid increment in
the strict path threshold, regardless of the number of path references. -/
theorem linearLift_accepts (n row delta x : ℤ) (s : Summary) :
    (linearLift n row delta s).need < x + row*delta ↔ s.need + delta < x := by
  simp only [linearLift, Int.add_mul, Int.one_mul]
  omega

#print axioms range_valid_of_bound
#print axioms range_bound_join
#print axioms summarize_correct
#print axioms valid_of_checked_summary
#print axioms linearLift_compose
#print axioms linearLift_accepts

end Compact3684
