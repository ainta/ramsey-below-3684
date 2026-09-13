"""Produce compact reflection witnesses; every emitted guard needs Lean checking.

The producer independently checks its new fixed-point profile/support choices.
It does NOT promote the external path checker to a trusted Lean component.
"""
import argparse
import array
from bisect import bisect_left, bisect_right
from fractions import Fraction as F
import gzip
import hashlib
import json
import mmap
from pathlib import Path
import tempfile
import time

from exact_profile import Profile, minimum, hull, decode, encode, ceilf, S
from verify_stream import prepare_paths, lines

Q = 10**18
WEIGHT = 10**12
LIFT = 10000
PAD = 50


class ReflectedProfile:
    def __init__(self, exact, epoch):
        original=[]
        for i, ((x,y),b) in enumerate(zip(exact.p,exact.sl)):
            a=y-x*b
            original.append((ceilf(a*Q)+epoch*LIFT,ceilf(b*Q)+epoch*LIFT,i))
        # Remove redundant lines after rounding. Each retained original line
        # has its own valid majorant proof; no equality of profiles is assumed.
        active=[]
        def cross(left,right):return F(right[0]-left[0],left[1]-right[1])
        for line in original:
            assert line[0]>0 and line[1]>0
            while active and active[-1][1]==line[1]:
                if active[-1][0]<=line[0]:break
                active.pop()
            if active and active[-1][1]==line[1]:continue
            while len(active)>1 and cross(active[-2],active[-1])>=cross(active[-1],line):active.pop()
            active.append(line)
        self.lines=active
        self.cross=[cross(l,r) for l,r in zip(active,active[1:])]
        self.intercepts=[line[0] for line in active]
        assert all(l[0]<r[0] and l[1]>r[1] for l,r in zip(active,active[1:]))
        assert all(x<y for x,y in zip(self.cross,self.cross[1:]))
        self.epoch=epoch

    def at(self,t):
        i=bisect_right(self.cross,t)
        a,b,_=self.lines[i]
        return F(a,Q)+F(b,Q)*t,i

    def support(self,a,b):
        # Targets in S-units, lines in Q-units. Round the weight upward:
        # this decreases the intercept; the slope guard is rechecked exactly.
        target_a=(a-PAD)*(Q//S)
        target_b=(b-PAD)*(Q//S)
        right=bisect_left(self.intercepts,target_a)
        if right==0:left=right;weight=0
        elif right==len(self.lines):left=right=len(self.lines)-1;weight=0
        else:
            left=right-1
            weight=ceilf(F((self.lines[right][0]-target_a)*WEIGHT,
                          self.lines[right][0]-self.lines[left][0]))
        assert 0<=weight<=WEIGHT
        la,lb,_=self.lines[left];ra,rb,_=self.lines[right]
        assert weight*la+(WEIGHT-weight)*ra<=WEIGHT*target_a, ('support-a',self.epoch,a,b,left,right)
        assert weight*(la+lb)+(WEIGHT-weight)*(ra+rb)<=WEIGHT*(target_a+target_b), ('support-at-one',self.epoch,a,b,left,right)
        return [left,right,weight]

    def json(self):
        return dict(epoch=self.epoch,scale=Q,lines=self.lines,
                    intersections=[encode(x) for x in self.cross])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--destination',type=Path,default=Path('certificates/reflected'))
    args=parser.parse_args()
    folder=Path('certificates/quantized')
    header=json.loads((folder/'bellman.json').read_text())
    grids={p['round']:p['N'] for p in header['profiles']}
    initial=json.loads((folder/'initial_u.json').read_text())
    P=Profile([(decode(x),decode(y)) for x,y in initial['points']])
    reflected=ReflectedProfile(P,0)
    root_lines=json.loads(Path('lean/Kernel/InitialTangents/manifest.json').read_text())['lines']
    for a,b,i in reflected.lines:assert root_lines[i][2:]==[a,b]
    catalog=json.loads((folder/'log_catalog.json').read_text())['entries']
    log_ids={arg:i for i,(arg,lo,hi) in enumerate(catalog)}
    assert len(log_ids)==len(catalog)
    args.destination.mkdir(parents=True,exist_ok=True)
    if (args.destination/'manifest.json').exists():raise SystemExit('Completed destination exists')
    (args.destination/'profile_00.json').write_text(json.dumps(reflected.json(),separators=(',',':')))
    values=[];costs=array.array('q');current=0;supports={};support_entries=[];round_reports=[]
    began=time.monotonic()
    output=gzip.open(args.destination/'records_00.jsonl.gz','wt',compresslevel=1)
    round_begin=0

    def finish_round(r):
        nonlocal P,reflected,supports,support_entries,output,round_begin
        output.close()
        N=grids[r];K=N*10**30
        outer=[];outer_json=[]
        for desc in (p for p in header['profiles'] if p['round']==r):
            st=decode(desc['start']);z=decode(desc['initial']);start=int(st*N)
            bound,input_line=reflected.at(st)
            assert bound<z, ('outer-input',r,start,bound,z)
            pts=[(st,z)]
            for row,node in enumerate(desc['references'],start+1):
                assert values[node]<z*K, ('outer-step',r,row,node)
                z+=F(costs[node],S*N);pts.append((F(row,N),z))
            assert z==decode(desc['endpoint'])
            outer.append(Profile(pts))
            outer_json.append(dict(start=start,initial=desc['initial'],input_line=input_line,
                                   references=desc['references']))
        candidate=P
        for new in outer:candidate=minimum(candidate,new)
        next_exact=hull(candidate)
        next_reflected=ReflectedProfile(next_exact,r+1)
        # Cover every interval of the minimum before taking its upper hull.
        # A cover uses one old valid line or one actual outer grid band.
        knots=[F(0)]+candidate.x
        assert knots[-1]==1 and all(x<y for x,y in zip(knots,knots[1:]))
        covers=[]
        for left,right in zip(knots,knots[1:]):
            mid=(left+right)/2
            choices=[(P.at(mid),-1,max(0,min(bisect_right(P.x,mid)-1,len(P.sl)-1)))]
            for j,new in enumerate(outer):
                if new.x[0]<=mid<=new.x[-1]:
                    choices.append((new.at(mid),j,bisect_right(new.x,mid)-1))
            _,which,segment=min(choices)
            if which<0:
                _,source_line=reflected.at(mid)
                aa,bb,_=reflected.lines[source_line]
                a,b=F(aa,Q),F(bb,Q)
                source=[0,source_line]
            else:
                profile=outer[which]
                x,y=profile.p[segment];b=profile.sl[segment];a=y-b*x
                source=[1,which,int(x*N)]
                assert x<=left<=right<=x+F(1,N)
            vl,il=next_reflected.at(left);vr,ir=next_reflected.at(right)
            assert a+b*left<=vl and a+b*right<=vr, ('cover',r,left,right,source)
            covers.append([encode(left),encode(right),source,il,ir])
        target=args.destination/f'round_{r:02d}.json'
        report=dict(round=r,N=N,record_start=round_begin,record_count=len(values)-round_begin,
                    support_pad=PAD,weight_scale=WEIGHT,supports=support_entries,
                    outer=outer_json,covers=covers)
        target.write_text(json.dumps(report,separators=(',',':')))
        (args.destination/f'profile_{r+1:02d}.json').write_text(json.dumps(next_reflected.json(),separators=(',',':')))
        summary=dict(round=r,records=report['record_count'],supports=len(support_entries),
                     covers=len(covers),lines=len(next_reflected.lines))
        round_reports.append(summary)
        print('PASS REFLECTION EXPORT',json.dumps(summary),flush=True)
        P=next_exact;reflected=next_reflected;supports={};support_entries=[];round_begin=len(values)
        if r+1<len(grids):output=gzip.open(args.destination/f'records_{r+1:02d}.jsonl.gz','wt',compresslevel=1)

    with tempfile.TemporaryDirectory(prefix='reflection_paths_',dir='.') as td:
        result=prepare_paths(header,folder,grids,Path(td))
        with result.open('rb') as source,mmap.mmap(source.fileno(),0,access=mmap.ACCESS_READ) as paths:
            for ix,rec in enumerate(lines(folder/header['record_file'])):
                rnd,row,col=rec['rank']
                if rnd!=current:finish_round(current);current=rnd
                N=grids[rnd];K=N*10**30
                vv=decode(rec['v'])*K;assert vv.denominator==1;v=int(vv)
                gap=decode(rec['end_gap'])*K;assert gap.denominator==1
                end=v-int(gap)
                u=int.from_bytes(paths[36*ix:36*ix+16],'little',signed=True)
                st=decode(rec['start'])*N;assert st.denominator==1;start=int(st)
                assert 0<start<=row<=N and 0<u<=end<v
                kind=rec['kind'];seed=rec.get('seed')
                common=dict(id=ix,row=row,col=col,start=start,v=v,end=end,u=u,
                            cost=rec['cost'],p=rec['p'],path=rec['path'],
                            log_blue=log_ids[S-rec['p']])
                log_blue=catalog[common['log_blue']]
                assert common['cost']*Q+S*log_blue[1]>0
                if kind=='weighted_path':
                    a,b,theta,mu,pi=seed
                    key=(a,b)
                    if key not in supports:
                        supports[key]=len(support_entries)
                        support_entries.append(dict(a=a,b=b,ab=reflected.support(a,b),ba=reflected.support(b,a)))
                    lmu,lone,lpi=[log_ids[x] for x in (mu,S-mu,pi)]
                    assert 0<pi<rec['p']<S and 0<mu<S and theta>0
                    assert (S-mu)*(a*Q+theta*catalog[lone][1])+S*S*catalog[lpi][1]>0
                    assert theta*u*Q+v*S*Q-a*K*Q-row*b*10**30*Q+theta*start*catalog[lmu][1]*10**30>0
                    common.update(kind=1,support=supports[key],seed=seed,logs=[lmu,lone,lpi])
                else:
                    assert kind=='unconditional_path'
                    base=rec['base']
                    if base['kind']=='input':
                        bound,index=reflected.at(F(start,N))
                        assert bound*K<u, ('input-base',ix)
                        common.update(kind=0,base=[0,index])
                    else:
                        assert base['kind']=='record' and 0<=base['child']<ix
                        assert values[base['child']]<u
                        common.update(kind=0,base=[1,base['child']])
                output.write(json.dumps(common,separators=(',',':'))+'\n')
                values.append(v);costs.append(rec['cost'])
                if (ix+1)%100000==0:print('EXPORTED RECORDS',ix+1,flush=True)
        finish_round(current)
    # No seed pad is needed at the terminal line; use padded inputs so the
    # same integer support-witness routine tests exactly the target line.
    final_support=reflected.support(544*S//1000+PAD,7622*S//10000+PAD)
    manifest=dict(status='EXPORTED_RECHECKED_WITNESSES_NOT_LEAN_THEOREM',records=len(values),
                  rounds=round_reports,final_support=final_support,elapsed_seconds=time.monotonic()-began,
                  record_source_sha256=hashlib.sha256((folder/header['record_file']).read_bytes()).hexdigest(),
                  note='Path starts are producer witnesses. Structural kernel validation remains mandatory.')
    (args.destination/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2),flush=True)


if __name__=='__main__':main()
