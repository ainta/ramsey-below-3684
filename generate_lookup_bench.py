"""Isolated lookup benchmarks; never imported by the actual proof.

Uses all real R07 node data and the first run-data file. The checked indices
use only that file. These are performance samples, not a completed round.
"""
import json
from pathlib import Path
from generate_profile_kernel import branch, emit


def tree_selector(name,names,typ,fanout=4):
    declarations=[]
    def choices(items):
        if len(items)==1:return items[0][1]
        middle=len(items)//2
        return f'(if i < {items[middle][0]} then {choices(items[:middle])} else {choices(items[middle:])})'
    def node(items,start):
        if len(items)<=fanout:
            body=branch(items,start)
        else:
            size=(len(items)+fanout-1)//fanout
            children=[(start+j,node(items[j:j+size],start+j)+' i') for j in range(0,len(items),size)]
            body=choices(children)
        helper=f'{name}Tree{len(declarations):05d}'
        declarations.append(f'def {helper} (i : Nat) : {typ} := {body}\n')
        return helper
    root=node(names,0)
    return ''.join(declarations)+f'def {name} (i : Nat) : {typ} := {root} i\n'


def main():
    manifest=json.loads(Path('lean/Kernel/ChainData/R07.json').read_text())
    nodes=[m for m in manifest['modules'] if '/R07N' in m]
    imports=nodes+['Kernel/ChainData/R07P0000']
    source=''.join('import '+m.replace('/','.')+'\n' for m in imports)
    source+='namespace Compact3684.LookupBench\nopen ChainData.R07\n'
    names=[f'nodeBlob{i:05d}' for i in range((manifest['records']+1023)//1024)]
    source+='def flat (i : Nat) : Chain.Packed.NodeBlob := '+branch(names)+'\n'
    groups=[]
    for start in range(0,len(names),16):
        name=f'group{start//16:03d}';groups.append(name)
        source+=f'def {name} (i : Nat) : Chain.Packed.NodeBlob := '+branch(names[start:start+16],start)+'\n'
    source+='def groups (i : Nat) : Nat → Chain.Packed.NodeBlob := '+branch(groups)+'\n'
    source+='def grouped (i : Nat) : Chain.Packed.NodeBlob := groups (i/16) i\n'
    source+='def runs (i : Nat) : Chain.Packed.RunBlob := '+branch([f'runBlob{i:05d}' for i in range(64)])+'\n'
    header=Path('lean/Kernel/ChainData/R07.lean').read_text()
    source+=next(line for line in header.splitlines() if line.startswith('def blockBlob :'))+'\n'
    source+='''def dataFor (nodes : Nat → Chain.Packed.NodeBlob) : Chain.Data :=
  { N := 6000, nodeCount := 501476, blockCount := 1097, runCount := 14234339,
    regionCount := 6879, oldLast := 0,
    node := fun i => Chain.Packed.nodeAt (nodes (i/1024)) (i%1024) (fun _ => ⟨0,0,0,0,0,0,0,0⟩),
    run := fun i => Chain.Packed.runAt (runs (i/1024)) (i%1024),
    block := fun i => Chain.Packed.blockAt blockBlob i,
    lookup := fun _ _ => 0, region := fun _ => ⟨0,0,0,0,0,0,0,0⟩,
    oldLine := fun _ => ⟨0,0⟩, log := fun _ => ⟨0,0,0⟩ }
end Compact3684.LookupBench
'''
    emit(Path('lean/LookupBench/Data.lean'),source)
    for name in ['flat','grouped']:
        code=f'''import LookupBench.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace Compact3684.LookupBench
theorem {name}_checked : (List.range 4096).all
    (fun i => Chain.runGuard (dataFor {name}) i) = true := by decide +kernel
#print axioms {name}_checked
end Compact3684.LookupBench
'''
        emit(Path(f'lean/LookupBench/{name.title()}.lean'),code)
    tree='import LookupBench.Data\nnamespace Compact3684.LookupBench\nopen ChainData.R07\n'
    tree+=tree_selector('tree',names,'Chain.Packed.NodeBlob')
    tree+='''set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
theorem tree_checked : (List.range 4096).all
    (fun i => Chain.runGuard (dataFor tree) i) = true := by decide +kernel
#print axioms tree_checked
end Compact3684.LookupBench
'''
    emit(Path('lean/LookupBench/Tree.lean'),tree)
    print('GENERATED TWO ISOLATED REAL-DATA PERFORMANCE SAMPLES',flush=True)


if __name__=='__main__':main()
