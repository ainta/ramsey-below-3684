"""Measure exact repeated path suffixes; diagnostic only, not a Lean proof.

The current verification keeps running. A shared suffix is identified by
exact interval endpoints and its exact successor, not by hash equality.
"""
import argparse
import gzip
import json
from pathlib import Path
import struct
import time


def measure(rnd,balanced=False):
    started=time.monotonic();intern={};leaves={};owner=None;path=[];runs=paths=maximum=0
    def finish():
        nonlocal paths,maximum
        if not path:return
        if balanced:
            level=[]
            for upper,lower in path:
                key=(upper<<19)+lower
                found=leaves.get(key)
                if found is None:
                    found=len(leaves)+len(intern)+1;leaves[key]=found
                level.append(found)
            while len(level)>1:
                following=[]
                for j in range(0,len(level)-1,2):
                    key=(level[j]<<32)+level[j+1]
                    found=intern.get(key)
                    if found is None:
                        found=len(leaves)+len(intern)+1
                        assert found<2**32
                        intern[key]=found
                    following.append(found)
                if len(level)%2:following.append(level[-1])
                level=following
            paths+=1;maximum=max(maximum,len(path));path.clear()
            return
        successor=0
        for upper,lower in reversed(path):
            key=(upper<<43)+(lower<<24)+successor
            found=intern.get(key)
            if found is None:
                found=len(intern)+1
                assert found<2**24
                intern[key]=found
            successor=found
        paths+=1;maximum=max(maximum,len(path));path.clear()
    with gzip.open(f'certificates/reflected_paths/runs_{rnd:02d}.bin.gz','rb') as stream:
        while True:
            data=stream.read(28*65536)
            if not data:break
            assert len(data)%28==0
            for start in range(0,len(data),28):
                current,upper,lower=struct.unpack_from('<III',data,start)
                if current!=owner:finish();owner=current
                assert upper<2**19 and lower<2**19
                path.append((upper,lower));runs+=1
    finish()
    return dict(round=rnd,original_runs=runs,unique_shared_nodes=len(intern)+len(leaves),
        unique_intervals=len(leaves) if balanced else None,balanced=balanced,
        sharing_factor=runs/(len(intern)+len(leaves)),nonempty_paths=paths,maximum_path_runs=maximum,
        elapsed_seconds=time.monotonic()-started,
        scope='Exact structural sharing measurement only; no new Lean theorem or guard result')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--round',type=int,nargs='+',required=True)
    parser.add_argument('--balanced',action='store_true')
    parser.add_argument('--report',type=Path,required=True);args=parser.parse_args();rows=[]
    for rnd in args.round:
        row=measure(rnd,args.balanced);rows.append(row);print(json.dumps(row),flush=True)
        args.report.write_text(json.dumps(dict(status='PATH_SHARING_MEASURED_NOT_PROVED',rounds=rows),indent=2)+'\n')


if __name__=='__main__':main()
