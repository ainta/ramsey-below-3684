import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R05NAll
import Kernel.ChainChecks.R05BAll
import Kernel.ChainChecks.R05PAll
import Kernel.OuterChecks.R05CAll
import Kernel.OuterChecks.R05SAll
import Kernel.OuterChecks.R05Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R05
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R05.data :=
  Chain.guards_of_checks CheckedChain.R05.all_nodeGuard CheckedChain.R05.all_blockGuard CheckedChain.R05.all_runGuard
    (fun i _ => Reflected.R05.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R05.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R05.initial CheckedOuter.R05.all_step
    Reflected.R06.all_shapes CheckedOuter.R05.all_cover CheckedOuter.R05.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R05.lines Reflected.R05.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R06.lines Reflected.R06.last) :=
  Outer.guards_sound (d := CheckedOuter.R05.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R05
