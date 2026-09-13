"""Generate packed kernel checks for the fixed-point initial support lines."""
import argparse
import hashlib
import json
from pathlib import Path

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--chunk-size',type=int,default=256)
    parser.add_argument('--limit',type=int)
    parser.add_argument('--destination',type=Path,default=Path('lean/Kernel/InitialTangents'))
    args=parser.parse_args()
    assert 1<=args.chunk_size<=256
    raw=Path('certificates/quantized/initial_tangents.json').read_bytes()
    witnesses=json.loads(raw)['entries'][:args.limit]
    entries=[]
    for n,d,an,ad,bn,bd in witnesses:
        aa=-((-an*10**18)//ad)
        bb=-((-bn*10**18)//bd)
        assert 0<n<2**40 and 0<d<2**40 and 0<aa<2**64 and 0<bb<2**64
        entries.append([n,d,aa,bb])
    args.destination.mkdir(parents=True,exist_ok=True)
    chunks=[]
    for start in range(0,len(entries),args.chunk_size):
        group=entries[start:start+args.chunk_size]
        payload=0
        for n,d,a,b in reversed(group):payload=(payload<<208)+n+(d<<40)+(a<<80)+(b<<144)
        name=f'C{start//args.chunk_size:04d}'
        source='import Kernel.Elementary\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
        source+=f'namespace Compact3684.InitialTangents.{name}\n'
        source+='def payload : Nat := '+hex(payload)+'\n'
        source+=f'theorem checked : (List.range {len(group)}).all (fun i => Elementary.initialLineGuard (Elementary.initialLineAt payload i)) = true := by decide +kernel\n'
        source+='#print axioms checked\n'
        source+=f'end Compact3684.InitialTangents.{name}\n'
        target=args.destination/(name+'.lean')
        if target.exists() and target.read_text()!=source:raise SystemExit('Different existing proof data')
        target.write_text(source)
        chunks.append(dict(module=str(target.with_suffix('').relative_to(Path('lean'))),start=start,
                           count=len(group),source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    manifest=dict(kind='INITIAL_TANGENTS',entries=len(entries),source_catalog_sha256=hashlib.sha256(raw).hexdigest(),
                  base_modules=['Kernel/Log18','Kernel/Elementary'],chunks=chunks,
                  fixed_point_scale=10**18,lines=entries)
    (args.destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('Generated',len(entries),'initial lines in',len(chunks),'kernel chunks',flush=True)

if __name__=='__main__':main()
