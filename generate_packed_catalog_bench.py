"""Emit a bounded packed-data integration benchmark, not a trusted result."""
import json
from pathlib import Path

def main():
    entries=json.loads(Path('certificates/quantized/log_catalog.json').read_text())['entries'][:1024]
    def signed(n):return 2*n if n>=0 else -2*n-1
    payload=0
    for n,lo,hi in reversed(entries):
        assert 0<=n<2**40 and 0<=signed(lo)<2**65 and 0<=signed(hi)<2**65
        payload=(payload<<170)+n+(signed(lo)<<40)+(signed(hi)<<105)
    source='import Kernel.Codec\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
    source+='namespace Compact3684.PackedCatalogBench\nopen Compact3684.Log18\n'
    source+='def payload : Nat := '+hex(payload)+'\n'
    source+='def entries : List CatalogEntry := Codec.packedCatalog 1024 payload\n'
    source+='theorem checked : entries.length = 1024 ∧ entries.all catalogGuard = true := by decide +kernel\n'
    source+='#print axioms checked\nend Compact3684.PackedCatalogBench\n'
    target=Path('lean/PackedNatCatalogBench.lean')
    if target.exists() and target.read_text()!=source:raise SystemExit('Different existing proof data')
    target.write_text(source)
    print('Generated',len(entries),'entries;',payload.bit_length(),'packed bits')

if __name__=='__main__':main()
