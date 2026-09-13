import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R06NAll
import Kernel.ChainChecks.R06BAll
import Kernel.ChainChecks.R06PAll
import Kernel.OuterChecks.R06CAll
import Kernel.OuterChecks.R06SAll
import Kernel.OuterChecks.R06Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R06
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R06.data :=
  Chain.guards_of_checks CheckedChain.R06.all_nodeGuard CheckedChain.R06.all_blockGuard CheckedChain.R06.all_runGuard
    (fun i _ => Reflected.R06.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R06.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R06.initial CheckedOuter.R06.all_step
    Reflected.R07.all_shapes CheckedOuter.R06.all_cover CheckedOuter.R06.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R06.lines Reflected.R06.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R07.lines Reflected.R07.last) :=
  Outer.guards_sound (d := CheckedOuter.R06.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R06
