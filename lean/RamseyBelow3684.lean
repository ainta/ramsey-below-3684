import ReflectedInitial
import CertifiedRound.R00
import CertifiedRound.R01
import CertifiedRound.R02
import CertifiedRound.R03
import CertifiedRound.R04
import CertifiedRound.R05
import CertifiedRound.R06
import CertifiedRound.R07
import TerminalStrict

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! End-to-end theorem. This module is valid only after every imported
concrete kernel-check assembly has been successfully built. -/
namespace Compact3684
open RamseyLean Filter

theorem final_profile_valid :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R08.lines Reflected.R08.last) :=
  CertifiedRound.R07.valid (CertifiedRound.R06.valid (CertifiedRound.R05.valid
    (CertifiedRound.R04.valid (CertifiedRound.R03.valid (CertifiedRound.R02.valid
      (CertifiedRound.R01.valid (CertifiedRound.R00.valid initial_reflected_valid)))))))

theorem ramsey_le_368395 :
    ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ (73679 / 20000 : ℝ)^k :=
  below_368395_of_affine (affine_of_final_profile final_profile_valid)

theorem ramsey_base_below_3684 :
    ∃ c : ℝ, c < 921/250 ∧ ∀ᶠ k : ℕ in atTop, (ramseyNumber k k : ℝ) ≤ c^k :=
  ⟨73679/20000,by norm_num,ramsey_le_368395⟩

#print axioms ramsey_le_368395
#print axioms ramsey_base_below_3684
end Compact3684
