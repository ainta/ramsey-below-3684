import Kernel.ChainData.R00
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.BenchR00
theorem column_guards : (List.range 1024).all (fun i => Chain.columnGuard ChainData.R00.data i) = true := by
  decide +kernel
theorem path_guards : (List.range 1024).all (fun i => Chain.pathGuard ChainData.R00.data i) = true := by
  decide +kernel
theorem block_guards : (List.range 163).all (fun i => Chain.blockGuard ChainData.R00.data i) = true := by
  decide +kernel
#print axioms column_guards
#print axioms path_guards
#print axioms block_guards
end Compact3684.BenchR00
