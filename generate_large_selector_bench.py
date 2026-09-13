"""Benchmark full selector size without waiting for unrelated literal files.

Only the first 4096 real runs are checked. Unselected leaves are uniquely
named dummy constants, so this is a performance sample, never a round proof.
"""
from pathlib import Path
from generate_chain_data import selector
from generate_lookup_bench import tree_selector
from generate_profile_kernel import emit


def main():
    count=(14234339+1023)//1024
    source='import LookupBench.Data\nnamespace Compact3684.LargeSelectorBench\nopen ChainData.R07\n'
    names=[]
    for i in range(count):
        if i<64:names.append(f'runBlob{i:05d}')
        else:
            name=f'unusedRun{i:05d}';names.append(name)
            source+=f'def {name} : Chain.Packed.RunBlob := ⟨{i},{i}⟩\n'
    source+=selector('groupedRuns',names,'Chain.Packed.RunBlob',True)
    source+=tree_selector('treeRuns',names,'Chain.Packed.RunBlob')
    source+='''def dataFor (runs : Nat → Chain.Packed.RunBlob) : Chain.Data :=
  { LookupBench.dataFor LookupBench.grouped with
    run := fun i => Chain.Packed.runAt (runs (i/1024)) (i%1024) }
end Compact3684.LargeSelectorBench
'''
    emit(Path('lean/LargeSelectorBench/Data.lean'),source)
    for label,name in [('Grouped','groupedRuns'),('Tree','treeRuns')]:
        source=f'''import LargeSelectorBench.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.LargeSelectorBench
theorem {name}_checked : (List.range 4096).all
    (fun i => Chain.runGuard (dataFor {name}) i) = true := by decide +kernel
#print axioms {name}_checked
end Compact3684.LargeSelectorBench
'''
        emit(Path(f'lean/LargeSelectorBench/{label}.lean'),source)
    print('GENERATED FULL-SIZE SELECTOR PERFORMANCE SAMPLES',count,'leaves',flush=True)


if __name__=='__main__':main()
