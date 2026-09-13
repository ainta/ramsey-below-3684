import Kernel.ChainGuard

namespace Compact3684.Chain
def nodeGuard (d : Data) (i : Nat) : Bool :=
  columnGuard d i && arithmeticGuard d i && baseGuard d i && pathGuard d i

theorem nodeGuard_sound {d : Data} {i : Nat} (h : nodeGuard d i = true) :
    columnGuard d i = true ∧ arithmeticGuard d i = true ∧ baseGuard d i = true ∧ pathGuard d i = true := by
  simpa only [nodeGuard,Bool.and_eq_true_iff,and_assoc] using h
end Compact3684.Chain
