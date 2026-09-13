"""Generate representative kernel arithmetic benchmarks for the shared log table.

This measures evaluation of the actual proposed interval computation. It does
not prove real-log soundness or certify the full Ramsey argument.
"""
import argparse
import json
import os
from pathlib import Path

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('catalog', type=Path)
    parser.add_argument('--count', type=int, default=1024)
    parser.add_argument('--selection', choices=['spread', 'smallest'], default='spread')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.catalog.read_text())
    entries = sorted(data['entries'])
    assert data['scale'] == 10**12 and data['interval_scale'] == 10**18
    assert 1 <= args.count <= 1024 and args.count <= len(entries)
    if args.selection == 'spread':
        selected = [entries[(len(entries)-1)*j//max(1,args.count-1)] for j in range(args.count)]
    else:
        selected = entries[:args.count]
    os.environ['RAMSEY_INTERVAL_DIGITS'] = '18'
    import interval_arithmetic as I
    source = Path('lean/IntegerLog.lean').read_text()
    source = source.replace('10000000000000000000000000000000000000000', str(I.Q))
    source = source.replace('series (timesPos u u) 50 0', 'series (timesPos u u) 20 0')
    source = source.replace('6931471805599453094172321214581765680718', str(I.LOG2[0]))
    source = source.replace('6931471805599453094172321214581765680819', str(I.LOG2[1]))
    source += '\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
    source += 'namespace Compact3684.Bench\n'
    source += 'structure CatalogEntry where\n  argument : Int\n  lo : Int\n  hi : Int\n'
    source += 'def catalogSample : List CatalogEntry := [\n'
    source += ',\n'.join(f'CatalogEntry.mk ({n}) ({lo}) ({hi})' for n,lo,hi in selected) + ']\n'
    source += '''def catalogGuard (entry : CatalogEntry) : Bool :=
  match logarithm entry.argument scale with
  | none => false
  | some bounds => decide (entry.lo ≤ bounds.1 ∧ bounds.2 ≤ entry.hi)
theorem checked_catalog_sample : catalogSample.all catalogGuard = true := by decide +kernel
#print axioms checked_catalog_sample
end Compact3684.Bench
'''
    args.output.write_text(source)
    print(json.dumps(dict(count=len(selected), selection=args.selection,
        total_catalog_entries=len(entries), minimum_argument=selected[0][0],
        maximum_argument=selected[-1][0], output=str(args.output)), indent=2))

if __name__ == '__main__':
    main()
