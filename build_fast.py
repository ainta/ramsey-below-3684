"""Sparse finite-DAG extraction; stream data, and leave all path checks to verifier."""
from build_certificate import *
from numba import njit

@njit(cache=True)
def trace_path(i,j,alpha,N,Z,Cost,FC,req,ids,length):
    a=np.empty(i-alpha,np.int32);u=Z[i,j]-1e-8
    for k in range(i-alpha):
        r=i-k
        if k==0:ci=FC[i,j]
        else:
            lo=0;hi=length[r]
            while lo<hi:
                m=(lo+hi)//2
                if req[r,m]<u:lo=m+1
                else:hi=m
            if lo==0:return a[:k],False
            ci=ids[r,lo-1]
        if ci<0:return a[:k],False
        a[k]=ci;u-=Cost[r,ci]/N
    return a,True

class FastBuild(Build):
    def __init__(self,prefix,out):
        super().__init__(prefix);self.out=out;self.count=0
        self.recordfile=gzip.open(str(out)+'.records.gz','wt',compresslevel=1)
        self.edgefile=gzip.open(str(out)+'.edges.gz','wb',compresslevel=1)
        self.rp=array.array('q');self.rd=array.array('i');self.rkind=array.array('b');self.rpad=array.array('q')
    def put(self,key,d,depth=0):
        d['rank']=list(key);ix=self.count;self.count+=1;self.record_ids[key[1],key[2]]=ix
        self.maxdepth=max(self.maxdepth,depth);self.rd.append(depth);self.rp.append(d['p'])
        self.rpad.append(d.get('padding',0));self.rkind.append(1 if d['kind'] in ['input','weaken_unconditional','unconditional_path'] else 0)
        self.minimum('stored_cost_blue',IA.add(IA.ri(d['cost'],S),IA.log_rat(S-d['p'],S))[0])
        self.recordfile.write(json.dumps(d,separators=(',',':'))+'\n')
        if ix%10000==0:print('RECORDS',self.count,'edges',self.edges,'seeds',self.seed_count,'round',self.rnd,flush=True)
        return ix
    def node(self,i,j):
        cached=int(self.record_ids[i,j])
        if cached>=0:return cached
        key=(self.rnd,i,j);T=self.tab;N=self.N;v=self.ratv(i,j);aidx=int(T['A'][i,j]);co=self.cost(i,j)
        assert T['R'][i,j]>0 and aidx!=0,(key,'invalid')
        d={'ratio':encode(F(i,N)),'v':encode(v),'cost':co}
        if aidx==-1:
            e=self.input.at(F(i,N))
            if v>e:
                d.update(kind='input',p=math.ceil(math.exp(-15.)*S)+16)
                self.minimum('input_margin',iv(v-e)[0]);return self.put(key,d)
            cand=np.flatnonzero((T['A'][i,:j]<0)&(T['R'][i,:j]>14.));assert len(cand),(key,'missing unconditional')
            jj=int(cand[0]);child=self.node(i,jj);assert v>self.ratv(i,jj) and self.rkind[child]
            d.update(kind='weaken_unconditional',child=child,p=math.ceil(math.exp(-15.)*S)+16)
            return self.put(key,d,self.rd[child]+1)
        alpha=aidx if aidx>0 else -aidx-2;assert 1<=alpha<=i
        cols,ok=trace_path(i,j,alpha,N,T['Z'],T['Cost'],T['FC'],T['req'],T['ids'],T['length']);assert ok
        rows=np.arange(i,alpha,-1,dtype=np.int32)
        refs=self.record_ids[rows,cols]
        for k in np.flatnonzero(refs<0):
            if self.record_ids[rows[k],cols[k]]<0:self.node(int(rows[k]),int(cols[k]))
        refs=self.record_ids[rows,cols];assert np.all(refs>=0)
        slopes=np.ceil(T['Cost'][rows,cols]*S).astype(np.int64)
        total=int(slopes.sum());u=v-F(1,10**8)-F(total,S*N)
        dp=max((self.rd[int(ci)]+1 for ci in refs),default=0)
        offset=self.edges;self.edges+=len(refs);self.edgefile.write(cols.astype('<u2').tobytes() if getattr(self,'columns',False) else refs.astype('<u4').tobytes())
        d.update(start=encode(F(alpha,N)),path=[offset,len(refs)],end_gap=encode(F(1,10**8)))
        if aidx<0:
            e=self.input.at(F(alpha,N))
            if u>e:
                d.update(kind='unconditional_path',base={'kind':'input'},p=math.ceil(math.exp(-15.)*S)+16);self.minimum('unconditional_start',iv(u-e)[0])
            else:
                cand=np.flatnonzero((T['A'][alpha]<0)&(T['R'][alpha]>14.)&(T['Z'][alpha]<float(u)));assert len(cand),(key,'uncond base')
                jj=int(cand[0]);child=self.node(alpha,jj);assert self.rkind[child]
                self.minimum('unconditional_start',iv(u-self.ratv(alpha,jj))[0]);dp=max(dp,self.rd[child]+1)
                d.update(kind='unconditional_path',base={'kind':'record','child':child},p=math.ceil(math.exp(-15.)*S)+16)
        else:
            seed,p=self.seed(F(alpha,N),F(i,N),u,v,float(T['Mu'][i,j]));d.update(kind='weighted_path',seed=seed,p=p)
        return self.put(key,d,dp)
    def round(self,rnd,filename=None):
        self.rnd=rnd;self.supportcache={};archive=np.load(filename or HERE/f'{self.prefix}_{rnd}.npz');self.tab={k:archive[k] for k in archive.files};archive.close();T=self.tab;self.N=N=int(T['N']);self.K=N*10**30
        self.record_ids=np.full(T['Z'].shape,-1,np.int32);profs=[]
        for k,start in enumerate([.05,.1,.2,.4,.6,.8]):
            assert T['outs'][k,-1]<10
            j0=round(start*N);x0=F(j0,N);ini=F(ceilf(self.input.at(x0)*10**30),10**30)+F(1,10**7);z=ini;pts=[(x0,z)];refs=[]
            for i in range(j0+1,N+1):
                j=int(T['which'][k,i]);assert j>=0
                node=self.node(i,j);self.minimum('outer_size',iv(z-self.ratv(i,j))[0]);slope=self.cost(i,j)
                self.minimum('outer_blue',IA.add(IA.ri(slope,S),IA.log_rat(S-self.rp[node],S))[0]);z+=F(slope,S*N)
                pts.append((F(i,N),z));refs.append(node)
            print('EXACT PROFILE',rnd,start,float(z),math.exp(float(z)),flush=True)
            profs.append(Profile(pts));self.profiles.append({'round':rnd,'start':encode(x0),'initial':encode(ini),'N':N,'references':refs,'endpoint':encode(z)})
        for p in profs:self.input=minimum(self.input,p)
        self.input=hull(self.input);self.recordfile.flush();self.edgefile.flush()
        print('ROUND PASS',rnd,'records',self.count,'gamma',float(self.input.at(F(1))),flush=True)
        # A checkpoint lists complete rounds. The streams are only final after closing.
        Path(str(self.out)+'.checkpoint.json').write_text(json.dumps({'round':rnd,'records':self.count,'edges':self.edges,'profiles':self.profiles,'input':[[encode(t),encode(z)] for t,z in self.input.p]}))
        gc.collect()
    def save(self,out):
        self.recordfile.close();self.edgefile.close()
        data={'format':'bellman_dag_stream_v3' if getattr(self,'columns',False) else 'bellman_dag_stream_v2','initial_kind':'GNNW_U_MAJORANT','initial_file':'initial_u.json','S':S,'records_count':self.count,'edge_count':self.edges,'edge_file':Path(str(out)+'.edges.gz').name,'record_file':Path(str(out)+'.records.gz').name,'profiles':self.profiles}
        Path(out).write_text(json.dumps(data,separators=(',',':')))
        rep={'status':'FINITE_CANDIDATE_EXTRACTED_PENDING_INDEPENDENT_VERIFICATION','records':self.count,'path_edges':self.edges,'weighted_seeds':self.seed_count,'maximum_dependency_depth':self.maxdepth,'minimum_margins':{k:IA.fmt(v) for k,v in self.mins.items()},'exponent':str(self.input.at(F(1))),'exponent_float':float(self.input.at(F(1))),'base_float':math.exp(float(self.input.at(F(1))))}
        Path(str(out)+'.generation.json').write_text(json.dumps(rep,indent=2));print(rep,flush=True)

from repair_methods import node as repaired_node,round_ as repaired_round,fast_seed
FastBuild.node=repaired_node
FastBuild.round=repaired_round
FastBuild.seed=fast_seed

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--prefix',default='dualfine');p.add_argument('--rounds',type=int,default=4);p.add_argument('--output',default='bellman.json');p.add_argument('--append',nargs='*',default=[]);a=p.parse_args();b=FastBuild(a.prefix,HERE/a.output)
    for r in range(a.rounds):b.round(r)
    for j,fn in enumerate(a.append):b.round(a.rounds+j,HERE/fn)
    b.save(HERE/a.output)
