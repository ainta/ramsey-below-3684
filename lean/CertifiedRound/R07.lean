import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R07NAll
import Kernel.ChainChecks.R07BAll
import Kernel.ChainChecks.R07PAll
import Kernel.OuterChecks.R07CAll
import Kernel.OuterChecks.R07SAll
import Kernel.OuterChecks.R07Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R07
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R07.data :=
  Chain.guards_of_checks CheckedChain.R07.all_nodeGuard CheckedChain.R07.all_blockGuard CheckedChain.R07.all_runGuard
    (fun i _ => Reflected.R07.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R07.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R07.initial CheckedOuter.R07.all_step
    Reflected.R08.all_shapes CheckedOuter.R07.all_cover CheckedOuter.R07.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R07.lines Reflected.R07.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R08.lines Reflected.R08.last) :=
  Outer.guards_sound (d := CheckedOuter.R07.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R07
