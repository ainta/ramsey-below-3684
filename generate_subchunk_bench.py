"""Kernel-cache pressure benchmark; identical checked range in smaller declarations."""
from pathlib import Path
from generate_chain_checks import case_proof,rechunk_source
from generate_profile_kernel import emit


def main():
    for size in [256,1024]:
        namespace=f'Compact3684.SubchunkBench.S{size}'
        source='import LargeSelectorBench.Data\nimport Kernel.CheckedProfiles\n'
        source+='set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
        source+=f'namespace {namespace}\nopen LargeSelectorBench\n'
        source+='def sampleData : Chain.Data := dataFor groupedRuns\n'
        chunks=[]
        for j,start in enumerate(range(0,4096,size)):
            source+=f'theorem checked{j:03d} : (List.range {size}).all (fun i => Chain.runGuard sampleData ({start}+i)) = true := by decide +kernel\n'
            source+=f'theorem at{j:03d} (i : Nat) (hl : {start} ≤ i) (hh : i < {start+size}) : Chain.runGuard sampleData i = true := checkedRange_at checked{j:03d} hl hh\n'
            chunks.append(dict(start=start,count=size,theorem=f'at{j:03d} i'))
        source+='theorem guard_at (i : Nat) (hl : 0 ≤ i) (hh : i < 4096) : Chain.runGuard sampleData i = true := by\n'
        source+=case_proof(chunks)
        source+='theorem checked : (List.range 4096).all (fun i => Chain.runGuard sampleData i) = true := by\n'
        source+='  apply List.all_eq_true.mpr\n  intro i hi\n  exact guard_at i (Nat.zero_le _) (List.mem_range.mp hi)\n'
        source+=f'#print axioms checked\nend {namespace}\n'
        emit(Path(f'lean/SubchunkBench/S{size}.lean'),source)
    source='''import LargeSelectorBench.Data
import Kernel.CheckedProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.SubchunkBench.Joined1024
def data : Chain.Data := LargeSelectorBench.dataFor LargeSelectorBench.groupedRuns
theorem checked : (List.range 4096).all (fun i => Chain.runGuard data (0+i)) = true := by decide +kernel
theorem guard_at (i : Nat) (hl : 0 ≤ i) (hh : i < 4096) : Chain.runGuard data i = true :=
  checkedRange_at checked hl hh
#print axioms checked
end Compact3684.SubchunkBench.Joined1024
'''
    emit(Path('lean/SubchunkBench/Joined1024.lean'),rechunk_source(source,0,4096,1024))
    print('GENERATED IDENTICAL 4096-RUN CHECK IN SMALLER KERNEL DECLARATIONS',flush=True)


if __name__=='__main__':main()
