#!/usr/bin/env python3
"""Independent verifier of the streamed finite certificate. No NumPy/optimizer."""
from pathlib import Path
from fractions import Fraction as F
import argparse,array,gzip,json,hashlib,sys,time,struct,subprocess,tempfile,shutil,mmap
import concurrent.futures,multiprocessing
from collections import deque
from exact_profile import Profile,root_profile,minimum,hull,decode,encode,S
if not __debug__:raise SystemExit('Run without -O.')
HERE=Path(__file__).resolve().parent
DEFAULT_ROOT=HERE/'input'/'ramsey_below_3_7'

def sha(path):
    h=hashlib.sha256()
    with open(path,'rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()

def lines(path):
    with gzip.open(path,'rt') as f:
        for line in f:yield json.loads(line)

def prepare_paths(d,folder,Ns,tmp,compare_paths=False):
    recfile=folder/d['record_file'];edgefile=folder/d['edge_file'];nodes=tmp/'nodes.bin';ed=tmp/'edges.bin';res=tmp/'paths.bin'
    n=0
    with nodes.open('wb') as f:
        for r in lines(recfile):
            rnd,row,col=r['rank'];assert rnd in Ns;K=Ns[rnd]*10**30;v=decode(r['v'])*K;assert v.denominator==1
            kind={'input':0,'weaken_unconditional':1,'weighted_path':2,'unconditional_path':3}[r['kind']]
            off,ln=r.get('path',[0,0]);end=v-decode(r['end_gap'])*K if kind>=2 else v;assert end.denominator==1
            base=r['child'] if kind==1 else (r['base'].get('child',-1) if kind==3 else -1)
            f.write(int(v).to_bytes(16,'little',signed=True)+int(end).to_bytes(16,'little',signed=True)+struct.pack('<qQ6i',r['cost'],off,ln,rnd,row,col,base,kind));n+=1
    assert n==d['records_count']
    with gzip.open(edgefile,'rb') as f,ed.open('wb') as g:shutil.copyfileobj(f,g,2**20)
    runs=d['format']=='bellman_dag_stream_v4_runs'
    ew=2 if d['format']=='bellman_dag_stream_v3' else 4
    assert ed.stat().st_size==ew*(d['run_count'] if runs else d['edge_count'])
    code=HERE/('check_runs.cpp' if runs else 'check_paths.cpp');binary=tmp/'check_paths'
    assert sys.byteorder=='little','Use a little-endian POSIX system for this accelerator.'
    subprocess.run(['g++','-O3','-std=c++17',str(code),'-o',str(binary)],check=True)
    subprocess.run([str(binary),str(nodes),str(ed),str(res),str(d['edge_count'] if runs else ew)],check=True)
    assert res.stat().st_size==36*n
    if compare_paths:
        assert runs, 'Expanded-path differential replay requires the v4 encoding.'
        import filecmp
        for source,name in [('expand_runs.cpp','expand'),('check_paths.cpp','original_check')]:
            subprocess.run(['g++','-O3','-std=c++17',str(HERE/source),'-o',str(tmp/name)],check=True)
        subprocess.run([str(tmp/'expand'),str(nodes),str(ed),str(tmp/'original_nodes'),str(tmp/'original_edges')],check=True)
        subprocess.run([str(tmp/'original_check'),str(tmp/'original_nodes'),str(tmp/'original_edges'),str(tmp/'original_result'),'2'],check=True)
        assert filecmp.cmp(res,tmp/'original_result',shallow=False), 'Run and expanded checkers disagree.'
        print('PASS byte-identical full expanded-path differential replay',flush=True)
    return res

def init_arithmetic(points,root,catalog=None):
    global WP,WI,WA0,WUP,WCACHE,WCATALOG
    import interval_arithmetic as I
    WP=Profile(points);WP.check_shape();WI=I;WUP=I.input_Up(10**9,S)
    WA0=I.sub(I.input_U(10**9,S),I.mul(I.ri(1,1000),WUP));WCACHE={};WCATALOG=catalog

def check_arithmetic_batch(batch):
    I=WI;lo_b=lo_d=lo_s=10**100;nseed=0
    def iv(x):return I.ri(x.numerator,x.denominator)
    def logq(n,d):
        if WCATALOG is None:return I.log_rat(n,d)
        assert d==S and n in WCATALOG, ('missing independently checked log entry',n,d)
        return WCATALOG[n]
    for ix,cost,p,t,u,v,seed,alpha in batch:
        blue=I.add(I.ri(cost,S),logq(S-p,S))[0];assert blue>0,('blue',ix,blue);lo_b=min(lo_b,blue)
        if seed is None:continue
        t,u,v,alpha=decode(t),decode(u),decode(v),decode(alpha);ai,bi,thi,mi,pi=seed;pad=100
        assert ai>pad and bi>0 and thi>0 and 0<mi<S and 0<pi<p<S
        a,b,th=F(ai,S),F(bi,S),F(thi,S);aw=I.ri(ai-pad,S);assert aw[0]>WA0[1] and aw[1]<WUP[0]
        if ai not in WCACHE:WCACHE[ai]=WP.seed_b(F(ai-pad,S))
        assert F(bi-pad,S)>=WCACHE[ai],('support',ix)
        rho=I.mul(I.ri(S-mi,S),I.add(iv(a),I.mul(iv(th),logq(S-mi,S))))
        dd=I.add(rho,logq(pi,S))[0];ss=I.add(iv(th*u+v-a-t*b),I.mul(iv(th*alpha),logq(mi,S)))[0]
        assert dd>0 and ss>0,('seed',ix,dd,ss);lo_d=min(lo_d,dd);lo_s=min(lo_s,ss);nseed+=1
    return lo_b,lo_d,lo_s,nseed

def verify(path,root,report,workers=3,compare_paths=False):
    path=Path(path);root=Path(root)
    import interval_arithmetic as I
    def iv(x):return I.ri(x.numerator,x.denominator)
    t0=time.monotonic();d=json.load(open(path));assert d['format'] in ['bellman_dag_stream_v2','bellman_dag_stream_v3','bellman_dag_stream_v4_runs'] and d['S']==S
    assert d['initial_kind']=='GNNW_U_MAJORANT' and d['initial_file']=='initial_u.json'
    initial_file=path.parent/d['initial_file']
    initial=json.loads(initial_file.read_text())
    from initial_profile import check_points
    check_points(initial['points'])
    catalog=None
    if 'log_catalog' in d:
        assert d['log_catalog']=='log_catalog.json'
        raw_catalog=json.loads((path.parent/d['log_catalog']).read_text())
        assert raw_catalog['scale']==S and raw_catalog['interval_scale']==I.Q
        catalog={}
        for j,(arg,lo,hi) in enumerate(raw_catalog['entries']):
            assert arg not in catalog and 0<arg<S
            exact=I.log_rat(arg,S)
            assert lo<=exact[0]<=exact[1]<=hi
            catalog[arg]=(lo,hi)
            if (j+1)%20000==0:print('PASS LOG CATALOG',j+1,flush=True)
        print('PASS all',len(catalog),'logarithm enclosures independently recomputed',flush=True)
    prs=d['profiles'];rounds=sorted(set(p['round'] for p in prs));assert rounds==list(range(len(rounds)))
    byround={r:[p for p in prs if p['round']==r] for r in rounds};Ns={r:byround[r][0]['N'] for r in rounds};assert all(p['N']==Ns[r] for r in rounds for p in byround[r])
    P=Profile([(decode(t),decode(v)) for t,v in initial['points']]);P.check_shape();U0=I.input_U(10**9,S);Up0=I.input_Up(10**9,S);A0=I.sub(U0,I.mul(I.ri(1,1000),Up0))
    assert iv(P.at(F(1,1000)))[0]>U0[1] and iv(P.sl[0])[1]<Up0[0]
    n=d['records_count'];vi=[];rows=array.array('i');rnds=array.array('i');costs=array.array('q');dens=array.array('q');flags=bytearray();depth=array.array('i');mins={};counts={};results=[];cache={};seed_count=0
    def lower(name,x):
        assert x>0,(name,x)
        mins[name]=min(mins.get(name,10**100),x)
    pool=None;pending=deque();batch=[]
    def start_pool():
        return concurrent.futures.ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('fork'),initializer=init_arithmetic,initargs=(P.p,str(root),catalog))
    def absorb(ans):
        nonlocal seed_count
        blue,den,size,nseed=ans;lower('blue_cost',blue)
        if nseed:lower('seed_density',den);lower('seed_size',size)
        seed_count+=nseed
    def submit():
        nonlocal batch
        if batch:pending.append(pool.submit(check_arithmetic_batch,batch));batch=[]
        if len(pending)>=4*workers:absorb(pending.popleft().result())
    def finish_round(r):
        nonlocal P,cache,pool
        submit()
        while pending:absorb(pending.popleft().result())
        pool.shutdown();pool=None
        N=Ns[r];K=N*10**30;outs=[];rr=[]
        for p in byround[r]:
            st=decode(p['start']);ini=decode(p['initial']);assert 0<st<1 and (st*N).denominator==1
            lower('outer_start',iv(ini-P.at(st))[0]);j0=int(st*N);assert len(p['references'])==N-j0
            z=ini;pts=[(st,z)]
            for j,ci in enumerate(p['references'],j0+1):
                assert 0<=ci<len(vi) and rnds[ci]==r and rows[ci]==j
                lower('outer_size',iv(z-F(vi[ci],K))[0]);z+=F(costs[ci],S*N);pts.append((F(j,N),z))
            assert z==decode(p['endpoint']);outs.append(Profile(pts));rr.append({'start':encode(st),'endpoint':encode(z),'exponent_decimal':I.fmt(z.numerator,z.denominator,30)})
        for q in outs:P=minimum(P,q)
        old=P;P=hull(P);P.check_shape()
        for t,z in old.p:assert P.at(t)>=z
        assert iv(P.at(F(1,1000)))[0]>U0[1] and iv(P.sl[0])[1]<Up0[0]
        gamma=min(decode(q['endpoint']) for q in rr);results.append({'round':r,'N':N,'profiles':rr,'best_exponent':encode(gamma),'support_endpoint':encode(P.at(F(1))),'support_knots':len(P.p)})
        cache={};print('PASS ROUND',r,'exponent',I.fmt(gamma.numerator,gamma.denominator,30),'records',len(vi),flush=True)
    with tempfile.TemporaryDirectory(prefix='ramsey_exact_paths_',dir=str(HERE)) as td:
        res=prepare_paths(d,path.parent,Ns,Path(td),compare_paths);f=res.open('rb');mm=mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ);current=0;pool=start_pool()
        for ix,rec in enumerate(lines(path.parent/d['record_file'])):
            rr,ii,jj=rec['rank'];assert rr in Ns
            if rr!=current:assert rr==current+1;finish_round(current);current=rr;pool=start_pool()
            N=Ns[rr];K=N*10**30;t=decode(rec['ratio']);v=decode(rec['v']);p=rec['p'];s=rec['cost'];kind=rec['kind']
            assert t==F(ii,N) and 0<t<=1 and v>0 and 0<p<S and s>0 and (v*K).denominator==1
            counts[kind]=counts.get(kind,0)+1
            pos=36*ix;u=F(int.from_bytes(mm[pos:pos+16],'little',signed=True),K);margin=int.from_bytes(mm[pos+16:pos+32],'little',signed=True);dep=struct.unpack_from('<i',mm,pos+32)[0];un=False
            if kind=='input':
                lower('input_size',iv(v-P.at(t))[0]);un=True;assert u==v and dep==0
            elif kind=='weaken_unconditional':
                ci=rec['child'];assert 0<=ci<ix and flags[ci] and rnds[ci]==rr and rows[ci]==ii and u==v and v*K>vi[ci];un=True;assert dep==depth[ci]+1
            else:
                assert kind in ['weighted_path','unconditional_path'];alpha=decode(rec['start']);gap=decode(rec['end_gap']);off,ln=rec['path'];assert 0<alpha<=t and gap>0 and (alpha*N).denominator==1 and ln==int((t-alpha)*N) and off>=0;assert 0<u<=v-gap
                if d['format']=='bellman_dag_stream_v4_runs':assert off<=d['run_count']
                else:assert off+ln<=d['edge_count']
                if ln:lower('path_size',I.ri(margin,K)[0])
                else:assert u==v-gap
                if kind=='unconditional_path':
                    base=rec['base']
                    if base['kind']=='input':lower('unconditional_start',iv(u-P.at(alpha))[0])
                    else:
                        assert base['kind']=='record';ci=base['child'];assert 0<=ci<ix and flags[ci] and rnds[ci]==rr and rows[ci]==int(alpha*N)
                        lower('unconditional_start',iv(u-F(vi[ci],K))[0])
                    un=True
                else:
                    assert len(rec['seed'])==5
            batch.append((ix,s,p,rec['ratio'],encode(u),rec['v'],rec.get('seed'),rec.get('start')))
            if len(batch)>=2000:submit()
            vi.append(int(v*K));rows.append(ii);rnds.append(rr);costs.append(s);dens.append(p);flags.append(int(un));depth.append(dep)
            if (ix+1)%10000==0:print('PASS RECORDS',ix+1,'/',n,flush=True)
        assert len(vi)==n;finish_round(current);mm.close();f.close()
    gamma=min(decode(p['endpoint']) for p in prs);e=I.exp_minus_unit(gamma.numerator,2*gamma.denominator);expint=I.div_positive(I.ONE,I.mul(e,e));digits=8;upper=I.ceil_div(expint[1]*10**digits,I.Q)
    lower('final_decimal',I.log_rat(upper,10**digits)[0]-iv(gamma)[1])
    from terminal_check import check_terminal
    terminal=check_terminal(P)
    # This deliberately simpler line is also the one in TerminalNumeric.lean.
    simple_terminal=check_terminal(P, affine=(F(544,1000),F(7622,10000))) if terminal['status']=='PASS_TARGET' else None
    Path(str(report)+'.profile.json').write_text(json.dumps({'points':[[encode(t),encode(v)] for t,v in P.p]},separators=(',',':')))
    ans={'status':'PASS_FINITE_CHAIN_NOT_LEAN','terminal':terminal,'simple_terminal':simple_terminal,'initial_majorant_sha256':sha(initial_file),'metadata_sha256':sha(path),'record_file_sha256':sha(path.parent/d['record_file']),'edge_file_sha256':sha(path.parent/d['edge_file']),
         'arithmetic':'exact fractions and directed integer intervals; path edges checked with overflow-checked C++ integers; floating point only selects a terminal cell, never certifies it',
         'interval_decimal_places':len(str(I.Q))-1,'logarithm_terms':I.NLOG,'verified_log_catalog_entries':len(catalog) if catalog is not None else None,
         'rounds':results,'records':n,'record_types':counts,'path_edges':d['edge_count'],'path_runs':d.get('run_count'),'expanded_path_differential_replay':compare_paths,'weighted_seeds':seed_count,'maximum_dependency_depth':max(depth),'exponent':encode(gamma),
         'exponent_decimal_lower':I.fmt(gamma.numerator,gamma.denominator,32),'exponent_decimal_upper':I.fmt(I.ceil_div(gamma.numerator*10**32,gamma.denominator),10**32,32),
         'base_lower':I.fmt(expint[0]),'base_upper':I.fmt(expint[1]+10**5),'strict_upper_base_decimal':I.fmt(upper,10**digits,8),'minimum_margins':{k:I.fmt(v) for k,v in mins.items()},'elapsed_seconds':time.monotonic()-t0,'arithmetic_workers':workers,
         'scope':'Finite analytic certificate conditional on the written graph-theoretic lemmas. No proof-system optimality or sub-3.6 claim.'}
    Path(report).write_text(json.dumps(ans,indent=2));print(json.dumps(ans,indent=2),flush=True);return ans
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('certificate',nargs='?',default=str(HERE/'bellman.json'));p.add_argument('--root',default=str(DEFAULT_ROOT));p.add_argument('--report',default=str(HERE/'verification_report.json'));p.add_argument('--workers',type=int,default=3);p.add_argument('--compare-paths',action='store_true');a=p.parse_args();assert a.workers>0;verify(a.certificate,a.root,a.report,a.workers,a.compare_paths)
