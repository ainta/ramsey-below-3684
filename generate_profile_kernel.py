"""Pack reflected profiles and their shared seed-region witnesses for Lean."""
import argparse
import hashlib
import json
from pathlib import Path

def branch(names,lo=0):
    if len(names)==1:return names[0]
    mid=len(names)//2
    return '(if i < '+str(lo+mid)+' then '+branch(names[:mid],lo)+' else '+branch(names[mid:],lo+mid)+')'

def emit(path,source):
    if path.exists():
        if path.read_text()!=source:raise SystemExit('Different generated data: '+str(path))
        return
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(source)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--chunk-size',type=int,default=512)
    args=parser.parse_args()
    size=args.chunk_size
    assert 1<=size<=1024
    folder=Path('certificates/reflected')
    manifests=[]
    for rnd in range(9):
        profile=json.loads((folder/f'profile_{rnd:02d}.json').read_text())
        lines=profile['lines'];names=[]
        namespace=f'Compact3684.Reflected.R{rnd:02d}'
        source='import Kernel.ProfileGuard\nnamespace '+namespace+'\n'
        for start in range(0,len(lines),1024):
            payload=0
            for a,b,_ in reversed(lines[start:start+1024]):
                assert 0<a<2**64 and 0<b<2**64
                payload=(payload<<128)+a+(b<<64)
            name=f'linePayload{len(names):03d}'
            names.append(name)
            source+='def '+name+' : Nat := '+hex(payload)+'\n'
        source+='def lineChunks (i : Nat) : Nat := '+branch(names)+'\n'
        source+='def lines (i : Nat) : ProfileCheck.Line := ProfileCheck.lineAt (lineChunks (i/1024)) (i%1024)\n'
        source+='def last : Nat := '+str(len(lines)-1)+'\n'
        source+='end '+namespace+'\n'
        module=f'Kernel/ProfileData/R{rnd:02d}'
        emit(Path('lean')/(module+'.lean'),source)
        chunks=[]
        for start in range(0,len(lines),size):
            count=min(size,len(lines)-start)
            name=f'R{rnd:02d}S{start//size:04d}'
            code='import '+module.replace('/','.')+'\n'
            code+='set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
            code+='namespace '+namespace+'.'+name+'\n'
            code+=f'theorem checked : (List.range {count}).all (fun i => ProfileCheck.shapeGuard lines last ({start}+i)) = true := by decide +kernel\n'
            code+='#print axioms checked\nend '+namespace+'.'+name+'\n'
            target=Path('lean/Kernel/ProfileShapes')/(name+'.lean')
            emit(target,code)
            chunks.append(dict(module=str(target.with_suffix('').relative_to('lean')),start=start,count=count,
                               source_sha256=hashlib.sha256(code.encode()).hexdigest()))
        manifests.append(dict(kind=f'PROFILE_SHAPE_{rnd}',entries=len(lines),chunks=chunks,base_modules=[module]))
        if rnd==8:continue
        regions=json.loads((folder/f'round_{rnd:02d}.json').read_text())['supports']
        chunks=[]
        for start in range(0,len(regions),size):
            group=regions[start:start+size];payload=0
            for row in reversed(group):
                a,b=row['a'],row['b'];i,j,w=row['ab'];k,l,v=row['ba']
                assert 0<a<2**48 and 0<b<2**48 and 0<=w<2**40 and 0<=v<2**40
                assert all(0<=x<2**16 for x in [i,j,k,l])
                payload=(payload<<240)+a+(b<<48)+(i<<96)+(j<<112)+(w<<128)+(k<<168)+(l<<184)+(v<<200)
            name=f'R{rnd:02d}G{start//size:04d}'
            code='import '+module.replace('/','.')+'\n'
            code+='set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
            code+='namespace '+namespace+'.'+name+'\n'
            code+='def payload : Nat := '+hex(payload)+'\n'
            code+=f'theorem checked : (List.range {len(group)}).all (fun i => ProfileCheck.regionGuard lines last (ProfileCheck.regionAt payload i)) = true := by decide +kernel\n'
            code+='#print axioms checked\nend '+namespace+'.'+name+'\n'
            target=Path('lean/Kernel/ProfileRegions')/(name+'.lean')
            emit(target,code)
            chunks.append(dict(module=str(target.with_suffix('').relative_to('lean')),start=start,count=len(group),
                               source_sha256=hashlib.sha256(code.encode()).hexdigest()))
        manifests.append(dict(kind=f'PROFILE_REGIONS_{rnd}',entries=len(regions),chunks=chunks,base_modules=[module]))
    target=Path('lean/Kernel/ProfileChecks')
    target.mkdir(exist_ok=True)
    for m in manifests:(target/(m['kind']+'.json')).write_text(json.dumps(m,indent=2)+'\n')
    combined=dict(kind='ALL_PROFILE_SHAPES_AND_REGIONS',entries=sum(m['entries'] for m in manifests),
                  chunks=[c for m in manifests for c in m['chunks']],
                  base_modules=[f'Kernel/ProfileData/R{i:02d}' for i in range(9)])
    (target/'manifest.json').write_text(json.dumps(combined,indent=2)+'\n')
    print('Generated',combined['entries'],'profile/region checks in',len(combined['chunks']),'chunks',flush=True)

if __name__=='__main__':main()
