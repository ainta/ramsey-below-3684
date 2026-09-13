import Ramsey3683Bootstrap.CheckedRoundInterface
import CheckedCatalogSound
import Kernel.ChainChecks.R00NAll
import Kernel.ChainChecks.R00BAll
import Kernel.ChainChecks.R00PAll
import Kernel.OuterChecks.R00CAll
import Kernel.OuterChecks.R00SAll
import Kernel.OuterChecks.R00Boundary
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Compact3684.CertifiedRound.R00
open RamseyLean Ramsey3683Bootstrap
theorem chain_guards : Chain.Guards CheckedChain.R00.data :=
  Chain.guards_of_checks CheckedChain.R00.all_nodeGuard CheckedChain.R00.all_blockGuard CheckedChain.R00.all_runGuard
    (fun i _ => Reflected.R00.all_regions i)
theorem outer_guards : Outer.Guards CheckedOuter.R00.data :=
  Outer.guards_of_checks (by decide) CheckedOuter.R00.initial CheckedOuter.R00.all_step
    Reflected.R01.all_shapes CheckedOuter.R00.all_cover CheckedOuter.R00.boundary
theorem valid (hF : UniformRamseyExpBound (ProfileCheck.profile Reflected.R00.lines Reflected.R00.last)) :
    UniformRamseyExpBound (ProfileCheck.profile Reflected.R01.lines Reflected.R01.last) :=
  Outer.guards_sound (d := CheckedOuter.R00.data) (by decide) hF Log18.CheckedCatalog.all_valid chain_guards outer_guards
#print axioms valid
end Compact3684.CertifiedRound.R00
