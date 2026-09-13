"""Emit bounded kernel-checkable chunks for every exact shared-log enclosure.

Generated Lean source is proof data, not a trusted result. A successful
chunk checks all of its arithmetic with `decide +kernel`.
"""
import argparse
import hashlib
import json
from pathlib import Path

def main():
    p = argparse.ArgumentParser()
    p.add_argument('catalog', type=Path)
    p.add_argument('--chunk-size', type=int, default=1024)
    p.add_argument('--destination', type=Path, default=Path('lean/Kernel/LogCatalog'))
    p.add_argument('--packed', action='store_true')
    args = p.parse_args()
    assert 1 <= args.chunk_size <= 1024
    raw = args.catalog.read_bytes()
    data = json.loads(raw)
    entries = data['entries']
    assert data['scale'] == 10**12 and data['interval_scale'] == 10**18
    assert len({n for n,_,_ in entries}) == len(entries)
    args.destination.mkdir(parents=True, exist_ok=True)
    records = []
    for start in range(0, len(entries), args.chunk_size):
        index = start // args.chunk_size
        chunk = entries[start:start+args.chunk_size]
        name = f'C{index:04d}'
        target = args.destination / (name + '.lean')
        namespace='Compact3684.Log18.Packed' if args.packed else 'Compact3684.Log18.Catalog'
        source = ('import Kernel.Codec\n' if args.packed else 'import Kernel.Log18\n')
        source += 'set_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
        source += f'namespace {namespace}.{name}\n'
        if args.packed:
            def signed(n):return 2*n if n>=0 else -2*n-1
            payload=0
            for n,lo,hi in reversed(chunk):
                assert 0<=n<2**40 and 0<=signed(lo)<2**65 and 0<=signed(hi)<2**65
                payload=(payload<<170)+n+(signed(lo)<<40)+(signed(hi)<<105)
            check=payload
            for n,lo,hi in chunk:
                assert check%2**40==n
                assert (check>>40)%2**65==signed(lo)
                assert (check>>105)%2**65==signed(hi)
                check>>=170
            assert check==0
            source+='def payload : Nat := '+hex(payload)+'\n'
            source+=f'def entries : List CatalogEntry := Compact3684.Codec.packedCatalog {len(chunk)} payload\n'
            source+=f'theorem checked : entries.length = {len(chunk)} ∧ entries.all catalogGuard = true := by decide +kernel\n'
            source+='theorem guards : entries.all catalogGuard = true := checked.2\n'
        else:
            source += 'def entries : List CatalogEntry := [\n'
            source += ',\n'.join(f'CatalogEntry.mk ({n}) ({lo}) ({hi})' for n,lo,hi in chunk)
            source += ']\n'
            source += 'theorem checked : entries.all catalogGuard = true := by decide +kernel\n'
        source += '#print axioms checked\n'
        source += f'end {namespace}.{name}\n'
        if target.exists() and target.read_text() != source:
            raise SystemExit(f'Refusing to replace different existing proof data: {target}')
        target.write_text(source)
        records.append(dict(module=str(target.with_suffix('').relative_to(Path('lean'))), start=start, count=len(chunk),
                            source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    manifest = dict(status='GENERATED_NOT_YET_KERNEL_CHECKED', entries=len(entries),
                    packed=args.packed, namespace=namespace,
                    source_catalog_sha256=hashlib.sha256(raw).hexdigest(), chunks=records)
    (args.destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({k:v for k,v in manifest.items() if k!='chunks'},indent=2))
    print('chunks:',len(records))

if __name__ == '__main__':
    main()
