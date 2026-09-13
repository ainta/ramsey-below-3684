import Kernel.ChainData.R00
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.Bench4096R00
theorem run_guards : (List.range 4096).all (fun i => Chain.runGuard ChainData.R00.data i) = true := by
  decide +kernel
#print axioms run_guards
end Compact3684.Bench4096R00
