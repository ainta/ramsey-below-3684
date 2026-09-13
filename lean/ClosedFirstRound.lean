import ReflectedInitial
import CertifiedRound.R00

namespace Compact3684
theorem first_round_uniform :
    RamseyLean.UniformRamseyExpBound (ProfileCheck.profile Reflected.R01.lines Reflected.R01.last) :=
  CertifiedRound.R00.valid initial_reflected_valid
#print axioms first_round_uniform
end Compact3684
