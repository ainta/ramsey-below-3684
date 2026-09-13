import InitialUniform
import Ramsey3683Bootstrap.ProfileCheck
import Kernel.RootLinksSound

set_option autoImplicit false
namespace Compact3684
open RamseyLean Ramsey3683Bootstrap

theorem initial_reflected_valid :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R00.lines Reflected.R00.last) := by
  apply Ramsey3683Bootstrap.UniformRamseyExpBound.affine_minimum
  intro i
  have hc := Elementary.initialLineGuard_sound (Elementary.CheckedInitial.all_entries i.val)
  have he := of_decide_eq_true (ReflectedRoot.all_checked i.val (by omega))
  apply initial_uniform.weakenRate
  intro r hr
  have hh := hc.2.2 r hr
  simpa only [ProfileCheck.Line.realLine, Elementary.InitialLine.realLine,
    AffineLine.eval, he.1, he.2] using hh

#print axioms initial_reflected_valid
end Compact3684
