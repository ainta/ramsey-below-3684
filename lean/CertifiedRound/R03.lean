import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R03NAll
import Kernel.ChainChecks.R03BAll
import Kernel.ChainChecks.R03PAll
import Kernel.OuterChecks.R03CAll
import Kernel.OuterChecks.R03SAll
import Kernel.OuterChecks.R03Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R03
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R03.data :=
  Chain.guards_of_checks CheckedChain.R03.all_nodeGuard CheckedChain.R03.all_blockGuard CheckedChain.R03.all_runGuard
    (fun i _ => Reflected.R03.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R03.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R03.initial CheckedOuter.R03.all_step
    Reflected.R04.all_shapes CheckedOuter.R03.all_cover CheckedOuter.R03.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R03.lines Reflected.R03.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R04.lines Reflected.R04.last) :=
  Outer.guards_sound (d := CheckedOuter.R03.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R03
