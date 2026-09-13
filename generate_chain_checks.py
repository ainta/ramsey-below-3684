"""Generate bounded kernel computations and balanced, hierarchical assemblies."""
import argparse
import hashlib
import json
from pathlib import Path
from generate_profile_kernel import emit as strict_emit

def rechunk_source(source,start,count,size):
    if count<=size:return source
    original=f'theorem checked : (List.range {count}).all (fun i => Chain.runGuard data ({start}+i)) = true := by decide +kernel\n'
    assert source.count(original)==1,'Only the unchanged generated run check may be transformed'
    pieces=[];code=''
    for offset in range(0,count,size):
        number=len(pieces);lo=start+offset;n=min(size,count-offset);name=f'checkedPart{number:03d}'
        code+=f'private theorem {name} : (List.range {n}).all (fun i => Chain.runGuard data ({lo}+i)) = true := by decide +kernel\n'
        pieces.append(dict(start=lo,count=n,name=name))
    def join(items):
        if len(items)==1:return items[0]['name']
        middle=len(items)//2;left=items[:middle];right=items[middle:]
        return '(checkedRange_join (f := Chain.runGuard data) '+f'(start := {items[0]["start"]}) '+\
            f'(left := {sum(x["count"] for x in left)}) (right := {sum(x["count"] for x in right)}) '+\
            join(left)+' '+join(right)+')'
    code+=original.replace('by decide +kernel\n','by\n  exact '+join(pieces)+'\n')
    return 'import Kernel.ChunkedChecks\n'+source.replace(original,code)


def rechunk_unbuilt(rnd,size):
    assert rnd>=5 and size>0
    path=Path(f'lean/Kernel/ChainChecks/R{rnd:02d}.json')
    manifest=json.loads(path.read_text());changes=[]
    for chunk in manifest['chunks']:
        if f'/R{rnd:02d}P' not in chunk['module']:continue
        source=Path('lean')/(chunk['module']+'.lean')
        old=source.read_text()
        assert hashlib.sha256(old.encode()).hexdigest()==chunk['source_sha256']
        assert not source.with_suffix('.olean').exists(),'Preserve every already checked module'
        if chunk.get('subchunk_size')==size:continue
        assert 'subchunk_size' not in chunk,'Refuse a second, ambiguous transformation'
        new=rechunk_source(old,chunk['start'],chunk['count'],size)
        changes.append((source,new,chunk))
    for source,new,chunk in changes:
        source.write_text(new)
        chunk['source_sha256']=hashlib.sha256(new.encode()).hexdigest()
        chunk['subchunk_size']=size
    manifest['subchunk_support']='Kernel/ChunkedChecks'
    path.write_text(json.dumps(manifest,indent=2)+'\n')
    print('RECHUNKED UNBUILT RUN FILES ONLY',rnd,len(changes),'size',size,flush=True)

def emit(path,source):
    # Mechanical migration of this generator's first, uncompiled output:
    # Lean reserves the identifier `at`.
    if path.exists():
        old=path.read_text()
        if old != source and old.replace('theorem at (','theorem guard_at (').replace('.at i','.guard_at i') == source:
            path.write_text(source)
            return
    strict_emit(path,source)

def case_proof(chunks,indent='  ',depth=0):
    if len(chunks)==1:
        c=chunks[0]
        return indent+'exact '+c['theorem']+' (by omega) (by omega)\n'
    mid=len(chunks)//2
    code=indent+f'by_cases h{depth} : i < {chunks[mid]["start"]}\n'
    return code+indent+'·\n'+case_proof(chunks[:mid],indent+'  ',depth+1)+indent+'·\n'+case_proof(chunks[mid:],indent+'  ',depth+1)

def generate(rnd,size,subchunk_size=1024):
    data=json.loads(Path(f'lean/Kernel/ChainData/R{rnd:02d}.json').read_text())
    meta=json.loads(Path(f'certificates/reflected_paths/manifest.json').read_text())['rounds'][rnd]
    ns=f'Compact3684.CheckedChain.R{rnd:02d}'
    base=f'Kernel/CheckedChainData/R{rnd:02d}'
    code=f'import Kernel.ChainData.R{rnd:02d}\nimport Kernel.CheckedCatalog\nimport Kernel.ChainChecks\nnamespace {ns}\n'
    code+=f'def data : Chain.Data := {{ ChainData.R{rnd:02d}.data with log := Log18.CheckedCatalog.entry }}\nend {ns}\n'
    emit(Path('lean')/(base+'.lean'),code)
    allchunks=[];summaries=[];finals=[]
    for kind,guard,count,batch in [('N','nodeGuard',data['records'],512),
                                 ('B','blockGuard',meta['blocks'],512),
                                 ('P','runGuard',data['runs'],size)]:
        chunks=[]
        for start in range(0,count,batch):
            number=start//batch;n=min(batch,count-start)
            module=f'Kernel/ChainChecks/R{rnd:02d}{kind}{number:05d}'
            name=f'{kind}{number:05d}'
            code=f'import {base.replace("/",".")}\nimport Kernel.CheckedProfiles\n'
            code+='set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
            code+=f'namespace {ns}.{name}\n'
            code+=f'theorem checked : (List.range {n}).all (fun i => Chain.{guard} data ({start}+i)) = true := by decide +kernel\n'
            code+=f'theorem guard_at (i : Nat) (hl : {start} ≤ i) (hh : i < {start+n}) : Chain.{guard} data i = true :=\n  checkedRange_at checked hl hh\n'
            code+=f'#print axioms checked\nend {ns}.{name}\n'
            if kind=='P' and rnd>=5 and subchunk_size:
                code=rechunk_source(code,start,n,subchunk_size)
            emit(Path('lean')/(module+'.lean'),code)
            chunk=dict(module=module,start=start,count=n,source_sha256=hashlib.sha256(code.encode()).hexdigest(),theorem=f'{ns}.{name}.guard_at i')
            if kind=='P' and rnd>=5 and subchunk_size:chunk['subchunk_size']=subchunk_size
            chunks.append(chunk)
        allchunks.extend(chunks)
        groups=[]
        for start in range(0,len(chunks),64):
            group=chunks[start:start+64];lo=group[0]['start'];hi=group[-1]['start']+group[-1]['count']
            name=f'{kind}Group{start//64:04d}'
            module=f'Kernel/ChainChecks/R{rnd:02d}{name}'
            code=''.join('import '+c['module'].replace('/','.')+'\n' for c in group)
            code+=f'namespace {ns}.{name}\n'
            code+=f'theorem guard_at (i : Nat) (hl : {lo} ≤ i) (hh : i < {hi}) : Chain.{guard} data i = true := by\n'
            code+=case_proof(group)+f'end {ns}.{name}\n'
            emit(Path('lean')/(module+'.lean'),code);summaries.append(module)
            groups.append(dict(module=module,start=lo,count=hi-lo,theorem=f'{ns}.{name}.guard_at i'))
        module=f'Kernel/ChainChecks/R{rnd:02d}{kind}All'
        code=''.join('import '+c['module'].replace('/','.')+'\n' for c in groups)
        code+=f'namespace {ns}\ntheorem all_{guard} (i : Nat) (hi : i < {count}) : Chain.{guard} data i = true := by\n'
        code+=case_proof(groups)+f'#print axioms all_{guard}\nend {ns}\n'
        emit(Path('lean')/(module+'.lean'),code);summaries.append(module);finals.append(module)
    manifest=dict(kind=f'CHAIN_{rnd}_ALL_GUARDS',entries=sum(c['count'] for c in allchunks),chunks=allchunks,
                  base_modules=['Kernel/ChainChecks',base],assemblies=summaries,finals=finals)
    if rnd>=5 and subchunk_size:manifest['subchunk_support']='Kernel/ChunkedChecks'
    Path(f'lean/Kernel/ChainChecks/R{rnd:02d}.json').write_text(json.dumps(manifest,indent=2)+'\n')
    Path(f'lean/Kernel/ChainChecks/R{rnd:02d}Assemblies.json').write_text(json.dumps(dict(modules=summaries),indent=2)+'\n')
    print('GENERATED CHECKS',rnd,len(allchunks),'batches',manifest['entries'],'guards',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--round',type=int,nargs='+',required=True)
    p.add_argument('--run-batch',type=int,default=4096)
    p.add_argument('--subchunk-size',type=int,default=1024)
    p.add_argument('--rechunk-unbuilt',action='store_true')
    a=p.parse_args()
    for rnd in a.round:
        if a.rechunk_unbuilt:rechunk_unbuilt(rnd,a.subchunk_size)
        else:generate(rnd,a.run_batch,a.subchunk_size)
