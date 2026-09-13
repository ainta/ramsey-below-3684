import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R01NAll
import Kernel.ChainChecks.R01BAll
import Kernel.ChainChecks.R01PAll
import Kernel.OuterChecks.R01CAll
import Kernel.OuterChecks.R01SAll
import Kernel.OuterChecks.R01Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R01
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R01.data :=
  Chain.guards_of_checks CheckedChain.R01.all_nodeGuard CheckedChain.R01.all_blockGuard CheckedChain.R01.all_runGuard
    (fun i _ => Reflected.R01.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R01.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R01.initial CheckedOuter.R01.all_step
    Reflected.R02.all_shapes CheckedOuter.R01.all_cover CheckedOuter.R01.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R01.lines Reflected.R01.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R02.lines Reflected.R02.last) :=
  Outer.guards_sound (d := CheckedOuter.R01.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R01
