import Kernel.CheckedInitial
import Kernel.ProfileData.R00

namespace Compact3684.ReflectedRoot
def guard (i : Nat) : Bool :=
  decide ((Reflected.R00.lines i).a = (Elementary.CheckedInitial.entry i).intercept ∧
    (Reflected.R00.lines i).b = (Elementary.CheckedInitial.entry i).slope)
end Compact3684.ReflectedRoot
