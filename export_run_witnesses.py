"""Recheck all paths using monotone column blocks and emit packed witnesses.

This is an independent exact producer/check, not the Lean soundness theorem.
No expanded 813-million-edge path is constructed.
"""
import argparse
from array import array
import gzip
import json
from pathlib import Path
import struct
import sys
import time

UNIT_COST=10**18

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--destination',type=Path,default=Path('certificates/reflected_paths'))
    args=parser.parse_args()
    assert sys.byteorder=='little'
    folder=Path('certificates/reflected')
    manifest=json.loads((folder/'manifest.json').read_text())
    original=json.loads(Path('certificates/quantized/bellman.json').read_text())
    args.destination.mkdir(parents=True,exist_ok=True)
    if (args.destination/'manifest.json').exists():raise SystemExit('Completed destination exists')
    with gzip.open(Path('certificates/quantized')/original['edge_file'],'rb') as f:
        packed=f.read()
    codes=memoryview(packed).cast('I')
    used=0;total=0;expanded=0;reports=[];began=time.monotonic()
    for rnd in range(8):
        meta=json.loads((folder/f'round_{rnd:02d}.json').read_text())
        offset=meta['record_start'];N=meta['N']
        records=[];columns={};lookup={}
        with gzip.open(folder/f'records_{rnd:02d}.jsonl.gz','rt') as f:
            for text in f:
                r=json.loads(text);ix=len(records)
                assert r['id']==offset+ix
                base=r.get('base',[-1,-1])
                child=base[1]-offset if base[0]==1 else -1
                row,col=r['row'],r['col']
                rec=(row,col,r['v'],r['cost']*UNIT_COST,r['u'],r['end'],r['start'],child,r['kind'],*r['path'])
                assert 0<row<=N and 0<=col<65536
                key=row*65536+col
                assert key not in lookup
                lookup[key]=ix;records.append(rec);columns.setdefault(col,[]).append(ix)
        assert len(records)==meta['record_count']
        blocks=[];block_ids=array('I',[0])*len(records);prefs=[0]*len(records)
        def finish_block(ids,col,direction):
            bid=len(blocks);lo=records[ids[0]][0];hi=records[ids[-1]][0]
            assert len(ids)==hi-lo+1
            blocks.append([lo,hi,col,int(direction>0)])
            pref=0;last_adjusted=None
            for ix in ids:
                row,c,v,cost,*_=records[ix]
                adjusted=v-pref
                if last_adjusted is not None:
                    assert adjusted>=last_adjusted if direction>0 else adjusted<=last_adjusted
                pref+=cost;prefs[ix]=pref;block_ids[ix]=bid;last_adjusted=adjusted
        for col,ids in columns.items():
            ids.sort(key=lambda ix:records[ix][0])
            active=[];direction=0
            for ix in ids:
                if active:
                    last=records[active[-1]];r=records[ix]
                    delta=r[2]-last[2]-last[3]
                    sign=(delta>0)-(delta<0)
                    if r[0]!=last[0]+1 or (direction and sign and direction!=sign):
                        finish_block(active,col,direction);active=[];direction=0
                    elif sign:direction=sign
                active.append(ix)
            if active:finish_block(active,col,direction)
        (args.destination/f'blocks_{rnd:02d}.json').write_text(json.dumps(blocks,separators=(',',':')))
        with gzip.open(args.destination/f'columns_{rnd:02d}.bin.gz','wb',compresslevel=1) as out:
            buf=bytearray()
            for ix,r in enumerate(records):
                buf+=struct.pack('<I',block_ids[ix])+prefs[ix].to_bytes(16,'little')
                if len(buf)>2**20:out.write(buf);buf.clear()
            out.write(buf)
        pathmeta=[];nr=0;minimum_margin=None;zero_paths=0
        with gzip.open(args.destination/f'runs_{rnd:02d}.bin.gz','wb',compresslevel=1) as out:
            buf=bytearray()
            for owner,r in enumerate(records):
                row,col,v,cost,u,end,start,base,kind,off,length=r
                assert off==used and length==row-start
                assert 0<u<=end<v
                if base>=0:
                    assert base<owner and records[base][8]==0 and records[base][0]==start
                    assert records[base][0]*65536+records[base][1]<row*65536+col, ('base-rank',rnd,owner,base)
                    assert records[base][2]<u
                run_begin=nr;consumed=0;x=end
                while consumed<length:
                    code=codes[used];used+=1
                    length0=code>>16;column=code&65535
                    assert 0<length0<=length-consumed
                    hi=row-consumed;low=hi-length0+1
                    assert hi<row or column<col
                    while low<=hi:
                        upper=lookup[hi*65536+column];bid=block_ids[upper]
                        block_lo,block_hi,block_col,increasing=blocks[bid]
                        assert block_col==column and block_lo<=hi<=block_hi
                        lo=max(low,block_lo);lower=lookup[lo*65536+column]
                        assert block_ids[lower]==bid
                        endpoint=upper if increasing else lower
                        pref_before=prefs[lower]-records[lower][3]
                        part_cost=prefs[upper]-pref_before
                        need=prefs[upper]+records[endpoint][2]-prefs[endpoint]+records[endpoint][3]
                        margin=x-need
                        assert margin>0 and x>part_cost, ('run-guard',rnd,owner,lo,hi)
                        minimum_margin=margin if minimum_margin is None else min(minimum_margin,margin)
                        assert 0<x<2**128
                        buf+=struct.pack('<III',owner,upper,lower)+x.to_bytes(16,'little')
                        nr+=1;x-=part_cost;hi=lo-1
                        if len(buf)>2**22:out.write(buf);buf.clear()
                    consumed+=length0
                assert consumed==length and x==u, ('path-exit',rnd,owner,x,u)
                zero_paths+=length==0
                pathmeta.append([run_begin,nr-run_begin])
                expanded+=length
                if (owner+1)%100000==0:print('PASS COMPACT PATHS',rnd,owner+1,'runs',nr,flush=True)
            out.write(buf)
        with gzip.open(args.destination/f'path_index_{rnd:02d}.bin.gz','wb',compresslevel=1) as out:
            for off,count in pathmeta:out.write(struct.pack('<QI',off,count))
        report=dict(round=rnd,records=len(records),blocks=len(blocks),runs=nr,zero_paths=zero_paths,
                    minimum_integer_margin=minimum_margin,run_record_bytes=28,column_record_bytes=20,
                    path_index_record_bytes=12)
        reports.append(report);total+=nr
        print('PASS ROUND PATH EXPORT',json.dumps(report),flush=True)
        del records,columns,lookup,prefs,block_ids,pathmeta
    assert used==len(codes)==original['run_count'] and expanded==original['edge_count']
    result=dict(status='PASS_INDEPENDENT_MONOTONE_RUN_REPLAY_NOT_LEAN',rounds=reports,
                original_runs=used,split_runs=total,expanded_edges=expanded,
                elapsed_seconds=time.monotonic()-began)
    (args.destination/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
