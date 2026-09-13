"""Generate a small blue-cost arithmetic benchmark, not a Ramsey certificate."""
import argparse
import gzip
import json
import os
from pathlib import Path

def main():
    p = argparse.ArgumentParser()
    p.add_argument('records', type=Path)
    p.add_argument('--count', type=int, default=64)
    p.add_argument('--digits', type=int, choices=[18,40], default=40)
    p.add_argument('--kernel', action='store_true')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    assert 0 < a.count <= 1024
    pairs=[]
    with gzip.open(a.records, 'rt') as f:
        for line in f:
            r=json.loads(line)
            if r['kind']=='weighted_path':
                pairs.append((r['cost'],r['p']))
                if len(pairs)==a.count:break
    assert len(pairs)==a.count
    source=Path('lean/IntegerLog.lean').read_text()
    if a.digits == 18:
        os.environ['RAMSEY_INTERVAL_DIGITS'] = '18'
        import interval_arithmetic as I
        source=source.replace('10000000000000000000000000000000000000000',str(I.Q))
        source=source.replace('series (timesPos u u) 50 0', 'series (timesPos u u) 20 0')
        source=source.replace('6931471805599453094172321214581765680718',str(I.LOG2[0]))
        source=source.replace('6931471805599453094172321214581765680819',str(I.LOG2[1]))
    source += '\nset_option maxRecDepth 100000\nset_option maxHeartbeats 1000000\n'
    source += 'namespace Compact3684.Bench\n'
    source += 'def inputs : List (Int × Int) := ['+',\n'.join(f'({c},{d})' for c,d in pairs)+']\n'
    source += 'theorem checked_blue_sample : inputs.all (fun p => blueGuard p.1 p.2) = true := by decide'+(' +kernel' if a.kernel else '')+'\n'
    source += '#print axioms checked_blue_sample\nend Compact3684.Bench\n'
    a.output.write_text(source)

if __name__=='__main__':main()
