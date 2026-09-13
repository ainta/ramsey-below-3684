"""Emit the exact outer-path and profile-cover data; recheck every integer guard.

The generated kernel computations, not these producer assertions, are trusted.
"""
import argparse
from array import array
import gzip
import hashlib
import json
from pathlib import Path
from exact_profile import decode,ceilf
from generate_chain_data import pack
from generate_profile_kernel import branch,emit
from generate_chain_checks import case_proof

S=10**12;Q=10**18;UNIT=10**30

def generate(rnd):
    folder=Path('certificates/reflected')
    info=json.loads((folder/f'round_{rnd:02d}.json').read_text())
    old=json.loads((folder/f'profile_{rnd:02d}.json').read_text())['lines']
    new=json.loads((folder/f'profile_{rnd+1:02d}.json').read_text())['lines']
    N=info['N'];K=N*UNIT;offset=info['record_start']
    costs=array('q');floors=[]
    with gzip.open(folder/f'records_{rnd:02d}.jsonl.gz','rt') as records:
        for text in records:
            r=json.loads(text);costs.append(r['cost']);floors.append(r['v'])
    values=[];refs=[];paths=[]
    for p in info['outer']:
        start=p['start'];initial=ceilf(decode(p['initial'])*K)
        vals=[0]*(N+1);ids=[0]*(N+1);vals[start]=initial
        a,b,_=old[p['input_line']]
        assert (a*N+b*start)*UNIT<initial*Q
        for row,ref in enumerate(p['references'],start):
            ix=ref-offset;assert 0<=ix<len(costs) and floors[ix]<vals[row]
            ids[row]=ix;vals[row+1]=vals[row]+costs[ix]*Q
        assert row==N-1
        paths.append(start+(p['input_line']<<16));values.extend(vals);refs.extend(ids)
    knots=[decode(c[0]) for c in info['covers']]+[decode(info['covers'][-1][1])]
    assert knots[0]==0 and knots[-1]==1
    words=[]
    for i,c in enumerate(info['covers']):
        l,r=knots[i:i+2];assert r==decode(c[1]) and 0<=l<r<=1
        kind,source,*rest=c[2];row=rest[0] if rest else 0
        if kind==0:a,b,_=old[source];den=Q
        else:
            assert kind==1 and 0<=source<len(paths) and info['outer'][source]['start']<=row<N
            index=source*(N+1)+row;cost=costs[refs[index]]
            a=values[index]-cost*row*Q;b=cost*Q*N;den=K
            assert row*l.denominator<=l.numerator*N
            assert r.numerator*N<=(row+1)*r.denominator
        for x,active in [(l,c[3]),(r,c[4])]:
            na,nb,_=new[active]
            if active>0:
                la,lb,_=new[active-1]
                assert (na-la)*x.denominator<=x.numerator*(lb-nb)
            if active+1<len(new):
                ra,rb,_=new[active+1]
                assert x.numerator*(nb-rb)<=(ra-na)*x.denominator
            assert (a*x.denominator+b*x.numerator)*Q <= (na*x.denominator+nb*x.numerator)*den,('cover',rnd,i,x)
        assert source<2**16 and row<2**13 and c[3]<2**16 and c[4]<2**16
        words.append(kind+(source<<1)+(row<<17)+(c[3]<<30)+(c[4]<<46))
    ns=f'Compact3684.CheckedOuter.R{rnd:02d}'
    data_modules=[];getters={}
    for kind,items,width in [('V',values,128),('I',refs,32),
                             ('K',[x.numerator+(x.denominator<<256) for x in knots],512),('C',words,64)]:
        names=[];decls=[];files=[]
        for start in range(0,len(items),1024):
            name=f'payload{kind}{len(names):04d}';names.append(name)
            decls.append('def '+name+' : Nat := '+hex(pack(items[start:start+1024],width))+'\n')
            if len(decls)==16 or start+1024>=len(items):
                module=f'Kernel/OuterData/R{rnd:02d}{kind}{len(files):03d}'
                source=f'import Kernel.PackedOuter\nnamespace {ns}\n'+''.join(decls)+f'end {ns}\n'
                emit(Path('lean')/(module+'.lean'),source);data_modules.append(module);files.append(module);decls=[]
        getters[kind]='def chunks'+kind+' (i : Nat) : Nat := '+branch(names)+'\n'
    base=f'Kernel/OuterData/R{rnd:02d}'
    code=f'import Kernel.CheckedChainData.R{rnd:02d}\nimport Kernel.ProfileAccess.R{rnd+1:02d}\n'
    code+=''.join('import '+m.replace('/','.')+'\n' for m in data_modules)
    code+=f'namespace {ns}\n'+''.join(getters.values())
    code+='def pathMetadata : Nat := '+hex(pack(paths,32))+'\n'
    code+=f'def path (p : Nat) : Outer.Path :=\n  {{ start := Chain.Packed.lookupAt pathMetadata p % 65536,\n'
    code+='    inputLine := Chain.Packed.lookupAt pathMetadata p / 65536,\n'
    code+=f'    value := fun j => Int.ofNat (Chain.Packed.read128 (chunksV ((p*{N+1}+j)/1024)) ((p*{N+1}+j)%1024)),\n'
    code+=f'    ref := fun j => Chain.Packed.lookupAt (chunksI ((p*{N+1}+j)/1024)) ((p*{N+1}+j)%1024) }}\n'
    code+=f'def data : Outer.Data :=\n  {{ chain := CheckedChain.R{rnd:02d}.data, pathCount := {len(paths)}, path := path,\n'
    code+=f'    newLast := Reflected.R{rnd+1:02d}.last, newLine := Reflected.R{rnd+1:02d}.lines, coverCount := {len(words)},\n'
    code+='    knot := fun i => Outer.Packed.fractionAt (chunksK (i/1024)) (i%1024),\n'
    code+='    cover := fun i => Outer.Packed.coverAt (chunksC (i/1024)) (i%1024) }\n'
    code+=f'end {ns}\n'
    emit(Path('lean')/(base+'.lean'),code);data_modules.append(base)
    chunks=[];assemblies=[];finals=[]
    # A flat outer step index retains the path/row predicate explicitly.
    specs=[('C',len(words),'Outer.coverGuard data','cover'),
           ('S',len(paths)*N,f'(fun i => Outer.indexedStepGuard data i)','step')]
    for kind,count,guard,label in specs:
        parts=[]
        for start in range(0,count,512):
            n=min(512,count-start);name=f'{kind}{start//512:04d}';module=f'Kernel/OuterChecks/R{rnd:02d}{name}'
            code=f'import {base.replace("/",".")}\nimport Kernel.CheckedProfiles\n'
            code+='set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
            code+=f'namespace {ns}.{name}\n'
            code+=f'theorem checked : (List.range {n}).all (fun i => {guard} ({start}+i)) = true := by decide +kernel\n'
            code+=f'theorem guard_at (i : Nat) (hl : {start} ≤ i) (hh : i < {start+n}) : {guard} i = true :=\n  checkedRange_at checked hl hh\n'
            code+=f'#print axioms checked\nend {ns}.{name}\n'
            emit(Path('lean')/(module+'.lean'),code)
            parts.append(dict(module=module,start=start,count=n,theorem=f'{ns}.{name}.guard_at i',source_sha256=hashlib.sha256(code.encode()).hexdigest()))
        chunks.extend(parts)
        module=f'Kernel/OuterChecks/R{rnd:02d}{kind}All'
        code=''.join('import '+c['module'].replace('/','.')+'\n' for c in parts)
        code+=f'namespace {ns}\ntheorem all_{label} (i : Nat) (hi : i < {count}) : {guard} i = true := by\n'
        code+=case_proof(parts)+f'end {ns}\n'
        emit(Path('lean')/(module+'.lean'),code);assemblies.append(module);finals.append(module)
    module=f'Kernel/OuterChecks/R{rnd:02d}Boundary'
    code=f'import {base.replace("/",".")}\nnamespace {ns}\n'
    code+='theorem boundary : Outer.boundaryGuard data = true := by decide +kernel\n'
    code+=f'theorem initial : (List.range {len(paths)}).all (fun p => Outer.initialGuard data.chain (data.path p)) = true := by decide +kernel\n'
    code+=f'end {ns}\n';emit(Path('lean')/(module+'.lean'),code);assemblies.append(module);finals.append(module)
    target=Path(f'lean/Kernel/OuterChecks/R{rnd:02d}.json')
    target.write_text(json.dumps(dict(kind=f'OUTER_{rnd}_GUARDS',entries=sum(c['count'] for c in chunks),chunks=chunks,
        base_modules=['Kernel/OuterGuard','Kernel/PackedOuter']+data_modules,assemblies=assemblies,finals=finals),indent=2)+'\n')
    Path(f'lean/Kernel/OuterChecks/R{rnd:02d}Assemblies.json').write_text(json.dumps(dict(modules=assemblies),indent=2)+'\n')
    print('EXPORTED OUTER',rnd,len(words),'covers',len(paths)*N,'step indices',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--round',type=int,nargs='+',required=True)
    for rnd in p.parse_args().round:generate(rnd)
