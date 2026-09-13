import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R04NAll
import Kernel.ChainChecks.R04BAll
import Kernel.ChainChecks.R04PAll
import Kernel.OuterChecks.R04CAll
import Kernel.OuterChecks.R04SAll
import Kernel.OuterChecks.R04Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R04
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R04.data :=
  Chain.guards_of_checks CheckedChain.R04.all_nodeGuard CheckedChain.R04.all_blockGuard CheckedChain.R04.all_runGuard
    (fun i _ => Reflected.R04.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R04.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R04.initial CheckedOuter.R04.all_step
    Reflected.R05.all_shapes CheckedOuter.R04.all_cover CheckedOuter.R04.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R04.lines Reflected.R04.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R05.lines Reflected.R05.last) :=
  Outer.guards_sound (d := CheckedOuter.R04.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R04
