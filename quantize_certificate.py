"""Untrusted control quantization with a small affine lift.

Proposal: E(t), v(t), b, cost -> E(t)+eps*t, v(t)+eps*t, b+eps, cost+eps.
Round mu and (1-p) DOWN on a relative grid of ratio at most 1+h, h<eps.
Every original path/outer margin loses only eps/N, not eps*path_length/N.
No proof of this transformation is trusted by the independent full replay.
"""
import argparse
from bisect import bisect_right
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import shutil
import interval_arithmetic as I
from exact_profile import decode, encode, S
from verify_stream import lines

EPS = F(18, 10**6)
H = F(16, 10**6)

def main():
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    p.add_argument('output', type=Path)
    a = p.parse_args()
    assert I.Q == 10**18
    a.output.parent.mkdir(parents=True, exist_ok=False)
    d = json.loads(a.source.read_text())
    assert d['format'] == 'bellman_dag_stream_v4_runs'
    eps = EPS*S
    assert eps.denominator == 1
    eps = int(eps)
    grid = [S]
    while True:
        next_value = I.ceil_div(grid[-1]*H.denominator, H.denominator+H.numerator)
        if next_value == grid[-1]:break
        grid.append(next_value)
    grid.reverse()
    def lower(n):
        k = bisect_right(grid, n)-1
        q = n if k < 0 else grid[k]
        assert 0 < q <= n and F(n,q) <= 1+H
        return q
    needed = set()
    record_name = a.output.name+'.records.gz'
    with gzip.open(a.output.parent/record_name, 'wt', compresslevel=1) as out:
        for ix,r in enumerate(lines(a.source.parent/d['record_file'])):
            r['cost'] += eps
            r['v'] = encode(decode(r['v'])+EPS*decode(r['ratio']))
            r['p'] = S-lower(S-r['p'])
            needed.add(S-r['p'])
            if r['kind']=='weighted_path':
                ai,bi,theta,mi,pi = r['seed']
                mi = lower(mi)
                pi = r['p']-1
                assert pi > 0
                r['seed'] = [ai,bi+eps,theta,mi,pi]
                needed.update([mi,S-mi,pi])
            out.write(json.dumps(r,separators=(',',':'))+'\n')
            if (ix+1)%200000==0:print('QUANTIZED',ix+1,'distinct_logs',len(needed),flush=True)
    for pr in d['profiles']:
        pr['initial'] = encode(decode(pr['initial'])+EPS*decode(pr['start']))
        pr['endpoint'] = encode(decode(pr['endpoint'])+EPS)
    raw = json.loads((a.source.parent/'initial_u.json').read_text())
    raw['points'] = [[t,encode(decode(v)+EPS*decode(t))] for t,v in raw['points']]
    raw['status'] = 'LIFTED_CANDIDATE_REQUIRES_FRESH_INITIAL_CHECK'
    (a.output.parent/'initial_u.json').write_text(json.dumps(raw,separators=(',',':')))
    edge_name = a.output.name+'.runs.gz'
    shutil.copyfile(a.source.parent/d['edge_file'],a.output.parent/edge_name)
    catalog=[]
    for j,n in enumerate(sorted(needed)):
        lo,hi = I.log_rat(n,S)
        catalog.append([n,lo,hi])
        if (j+1)%20000==0:print('CATALOG',j+1,'/',len(needed),flush=True)
    catname='log_catalog.json'
    (a.output.parent/catname).write_text(json.dumps(dict(
        scale=S,interval_scale=I.Q,entries=catalog),separators=(',',':')))
    d.update(record_file=record_name,edge_file=edge_name,log_catalog=catname,
             proposal_affine_lift=encode(EPS),proposal_relative_grid=encode(H))
    a.output.write_text(json.dumps(d,separators=(',',':')))
    report=dict(status='QUANTIZED_PENDING_INDEPENDENT_REPLAY',records=d['records_count'],
                distinct_logarithms=len(needed),
                affine_lift=str(EPS),relative_grid=str(H))
    (a.output.parent/'quantization.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
