import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R02NAll
import Kernel.ChainChecks.R02BAll
import Kernel.ChainChecks.R02PAll
import Kernel.OuterChecks.R02CAll
import Kernel.OuterChecks.R02SAll
import Kernel.OuterChecks.R02Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R02
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R02.data :=
  Chain.guards_of_checks CheckedChain.R02.all_nodeGuard CheckedChain.R02.all_blockGuard CheckedChain.R02.all_runGuard
    (fun i _ => Reflected.R02.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R02.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R02.initial CheckedOuter.R02.all_step
    Reflected.R03.all_shapes CheckedOuter.R02.all_cover CheckedOuter.R02.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R02.lines Reflected.R02.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R03.lines Reflected.R03.last) :=
  Outer.guards_sound (d := CheckedOuter.R02.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R02
