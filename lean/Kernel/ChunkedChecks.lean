import Kernel.CheckedProfiles

set_option autoImplicit false
namespace Compact3684

/-- Combine already kernel-checked adjacent ranges without evaluating them
again in one large kernel cache. The predicate and range are unchanged. -/
theorem checkedRange_join {f : Nat → Bool} {start left right : Nat}
    (hl : (List.range left).all (fun j => f (start+j)) = true)
    (hr : (List.range right).all (fun j => f (start+left+j)) = true) :
    (List.range (left+right)).all (fun j => f (start+j)) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hj' := List.mem_range.mp hj
  by_cases h : j < left
  · exact checkedRange_at hl (by omega) (by omega)
  · exact checkedRange_at hr (by omega) (by omega)

#print axioms checkedRange_join
end Compact3684
