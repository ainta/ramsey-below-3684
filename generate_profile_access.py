"""Assemble checked profile predicates without recomputing large guard lists."""
import json
from pathlib import Path
from generate_profile_kernel import branch,emit

def cases(chunks,namespace,indent='  ',depth=0):
    if len(chunks)==1:
        c=chunks[0];name=c['module'].rsplit('/',1)[1]
        return indent+'exact checkedRange_at '+namespace+'.'+name+'.checked (by omega) (by omega)\n'
    mid=len(chunks)//2;boundary=chunks[mid]['start']
    code=indent+f'by_cases h{depth} : i < {boundary}\n'
    code+=indent+'·\n'+cases(chunks[:mid],namespace,indent+'  ',depth+1)
    code+=indent+'·\n'+cases(chunks[mid:],namespace,indent+'  ',depth+1)
    return code

def main():
    for rnd in range(9):
        ns=f'Compact3684.Reflected.R{rnd:02d}'
        shape=json.loads(Path(f'lean/Kernel/ProfileChecks/PROFILE_SHAPE_{rnd}.json').read_text())
        source='import Kernel.CheckedProfiles\n'
        source+=''.join('import '+c['module'].replace('/','.')+'\n' for c in shape['chunks'])
        region=None
        if rnd<8:
            region=json.loads(Path(f'lean/Kernel/ProfileChecks/PROFILE_REGIONS_{rnd}.json').read_text())
            source+=''.join('import '+c['module'].replace('/','.')+'\n' for c in region['chunks'])
        source+='namespace '+ns+'\n'
        source+='theorem all_shapes (i : Nat) (hi : i ≤ last) : ProfileCheck.shapeGuard lines last i = true := by\n'
        source+=f'  change i ≤ {shape["entries"]-1} at hi\n'
        source+=cases(shape['chunks'],ns)
        if region is not None:
            names=[]
            for i,c in enumerate(region['chunks']):
                old=c['module'].rsplit('/',1)[1]
                name=f'regionChunk{i:03d}';names.append(name)
                source+=f'def {name} : ProfileCheck.CheckedRegionChunk lines last := ⟨{c["count"]}, {old}.payload, by decide, {old}.checked⟩\n'
            source+='def regionChunks (i : Nat) : ProfileCheck.CheckedRegionChunk lines last := '+branch(names)+'\n'
            size=region['chunks'][0]['count']
            source+=f'def region (i : Nat) : ProfileCheck.RegionWitness := (regionChunks (i/{size})).entry (i%{size})\n'
            source+=f'theorem all_regions (i : Nat) : ProfileCheck.regionGuard lines last (region i) = true :=\n  (regionChunks (i/{size})).entry_guard (i%{size})\n'
            source+='#print axioms all_regions\n'
        source+='#print axioms all_shapes\nend '+ns+'\n'
        emit(Path(f'lean/Kernel/ProfileAccess/R{rnd:02d}.lean'),source)
    initial=json.loads(Path('lean/Kernel/InitialTangents/manifest.json').read_text())
    source='import Kernel.CheckedProfiles\n'
    source+=''.join('import '+c['module'].replace('/','.')+'\n' for c in initial['chunks'])
    source+='namespace Compact3684.Elementary.CheckedInitial\n'
    names=[]
    for i,c in enumerate(initial['chunks']):
        old='Compact3684.InitialTangents.'+c['module'].rsplit('/',1)[1]
        name=f'chunk{i:03d}';names.append(name)
        source+=f'def {name} : CheckedInitialChunk := ⟨{c["count"]}, {old}.payload, by decide, {old}.checked⟩\n'
    source+='def chunks (i : Nat) : CheckedInitialChunk := '+branch(names)+'\n'
    source+='def entry (i : Nat) : InitialLine := (chunks (i/256)).entry (i%256)\n'
    source+='theorem all_entries (i : Nat) : initialLineGuard (entry i) = true := (chunks (i/256)).entry_guard (i%256)\n'
    source+='#print axioms all_entries\nend Compact3684.Elementary.CheckedInitial\n'
    emit(Path('lean/Kernel/CheckedInitial.lean'),source)
    print('Generated 9 profile-access assemblies and checked initial access',flush=True)

if __name__=='__main__':main()
