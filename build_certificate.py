"""Extract and check a finite rational proof DAG from exploratory Bellman tables."""
from exact_profile import *
import numpy as np,math,time,sys,hashlib,gc,argparse,array
HERE=Path(__file__).resolve().parent
ROOT=Path(__file__).resolve().parents[1]/'input'/'ramsey_below_3_7'
sys.path.insert(0,str(ROOT/'ramsey_candidate_continuation_release'))
import interval_arithmetic as IA
sys.setrecursionlimit(20000)

def iv(x):return IA.ri(x.numerator,x.denominator)
def exact_ceil_float(x,scale=S):return math.ceil(x*scale)

def root_cached():
    path=HERE/'root_profile_exact.json'
    if path.exists():return Profile([(decode(a),decode(b)) for a,b in json.load(open(path))])
    return root_profile(ROOT)

class Build:
    def __init__(self,prefix):
        self.prefix=prefix;self.records=[];self.proofs=[];self.profiles=[];self.mem={};self.input=root_cached();self.supportcache={};self.tables=[];self.mins={};self.seed_count=0;self.edges=0;self.status={};self.rnd=0;self.maxdepth=0;self.blues={};self.vints={};self.edge_array=array.array('I')
        self.Up0=IA.input_Up(10**9,S);self.U0=IA.input_U(10**9,S);self.A0=IA.sub(self.U0,IA.mul(IA.ri(1,1000),self.Up0))
    def minimum(self,name,x):
        assert x>0,(name,x)
        self.mins[name]=min(self.mins.get(name,10**100),x)
    def ratv(self,i,j):return F(ceilf(F(str(float(self.tab['Z'][i,j])))*10**30),10**30)
    def cost(self,i,j):return math.ceil(self.tab['Cost'][i,j]*S)
    def put(self,key,d,depth=0):
        d['rank']=list(key);ix=len(self.records);self.records.append(d);self.mem[key]=ix;self.maxdepth=max(self.maxdepth,depth);self.status[ix]=depth
        self.blues[ix]=IA.add(IA.ri(d['cost'],S),IA.log_rat(S-d['p'],S))[0]
        self.minimum('stored_cost_blue',self.blues[ix]);self.vints[ix]=ceilf(decode(d['v'])*self.K)
        if len(self.records)%1000==0:print('RECORDS',len(self.records),'edges',self.edges,'seeds',self.seed_count,'round',self.rnd,flush=True)
        return ix
    def seed(self,alpha,end,u,v,mu):
        ai=None;ts=self.tab['ts'];zs=self.tab['zs'];D=float(u)+float(alpha)*math.log(mu);C=-math.log1p(-mu);tau=(C-D)/(float(end)*C);tt=min(tau,1/tau)
        assert D>0 and tau>0 and tt>=ts[0]
        j=max(0,min(np.searchsorted(ts,tt,side='right')-1,len(ts)-2))
        sl=(zs[j+1]-zs[j])/(ts[j+1]-ts[j]);value=zs[j]+sl*(tt-ts[j]);aa=sl if tau<=1 else value-tt*sl
        ai=round(aa*S);pad=100
        if ai not in self.supportcache:self.supportcache[ai]=ceilf(self.input.seed_b(F(ai-pad,S))*S)+pad
        bi=self.supportcache[ai];mi=round(mu*S)
        assert 0<mi<S and ai>pad and bi>0
        aw=IA.ri(ai-pad,S);assert aw[0]>self.A0[1] and aw[1]<self.Up0[0],('short support window',self.rnd,ai)
        a=F(ai,S);b=F(bi,S);lnm=IA.log_rat(mi,S);Dint=IA.add(iv(u),IA.mul(iv(alpha),lnm));assert Dint[0]>0
        num=iv(a+end*b-v)
        thi=IA.ceil_div((num[1]+IA.Q//10**12)*S,Dint[0]);assert thi>0
        th=F(thi,S)
        rho=IA.mul(IA.ri(S-mi,S),IA.add(iv(a),IA.mul(iv(th),IA.log_rat(S-mi,S))))
        assert rho[0]>0,('rho',self.rnd,alpha,end,v)
        pi=math.ceil(math.exp(-rho[0]/IA.Q)*S)+8;p0=pi+16;assert p0<S
        den=IA.add(rho,IA.log_rat(pi,S));self.minimum('seed_density',den[0])
        budget=IA.add(iv(th*u+v-a-end*b),IA.mul(iv(th*alpha),lnm));self.minimum('seed_size',budget[0])
        self.seed_count+=1
        return [ai,bi,thi,mi,pi],p0
    def node(self,i,j):
        key=(self.rnd,i,j)
        if key in self.mem:return self.mem[key]
        T=self.tab;N=self.N;v=self.ratv(i,j);aidx=int(T['A'][i,j]);co=self.cost(i,j)
        assert T['R'][i,j]>0 and aidx!=0,(key,'invalid')
        d={'ratio':encode(F(i,N)),'v':encode(v),'cost':co}
        if aidx==-1:
            e=self.input.at(F(i,N))
            if v>e:
                d.update(kind='input',p=math.ceil(math.exp(-15.)*S)+16)
                self.minimum('input_margin',iv(v-e)[0]);return self.put(key,d)
            cand=np.flatnonzero((T['A'][i,:j]<0)&(T['R'][i,:j]>14.))
            assert len(cand),('missing uncond reference',key,float(v-e))
            jj=int(cand[0]);child=self.node(i,jj);cv=decode(self.records[child]['v']);assert v>cv
            d.update(kind='weaken_unconditional',child=child,p=math.ceil(math.exp(-15.)*S)+16)
            return self.put(key,d,self.status[child]+1)
        alpha=aidx if aidx>0 else -aidx-2
        assert 1<=alpha<=i
        ur=float(T['Z'][i,j])-1e-8;u=v-F(1,10**8);path=[];dp=0
        urint=int(u*self.K);costsum=0;required=-10**100
        for r in range(i,alpha,-1):
            if r==i:ci=int(T['FC'][i,j])
            else:
                ln=int(T['length'][r]);kk=np.searchsorted(T['req'][r,:ln],ur,side='left')-1
                assert kk>=0,('missing step',key,r,ur)
                ci=int(T['ids'][r,kk])
            assert ci>=0 and (r<i or ci<j),('DAG order',key,r,ci)
            child=self.node(r,ci);slope=self.cost(r,ci);c=self.records[child]
            ur-=T['Cost'][r,ci]/N;costsum+=slope*(self.K//(S*N))
            required=max(required,self.vints[child]+costsum)
            path.append(child);dp=max(dp,self.status[child]+1)
        self.edges+=len(path)
        if path:self.minimum('path_size',IA.ri(urint-required,self.K)[0])
        u=F(urint-costsum,self.K)
        offset=len(self.edge_array);self.edge_array.extend(path)
        d.update(start=encode(F(alpha,N)),path=[offset,len(path)],end_gap=encode(F(1,10**8)))
        if aidx<0:
            at=F(alpha,N);e=self.input.at(at)
            if u>e:
                d.update(kind='unconditional_path',base={'kind':'input'},p=math.ceil(math.exp(-15.)*S)+16)
                self.minimum('unconditional_start',iv(u-e)[0])
            else:
                cand=np.flatnonzero((T['A'][alpha]<0)&(T['R'][alpha]>14.)&(T['Z'][alpha]<float(u)))
                assert len(cand),('missing starting bound',key,alpha,float(u-e))
                jj=int(cand[0]);child=self.node(alpha,jj);cv=decode(self.records[child]['v']);self.minimum('unconditional_start',iv(u-cv)[0]);dp=max(dp,self.status[child]+1)
                d.update(kind='unconditional_path',base={'kind':'record','child':child},p=math.ceil(math.exp(-15.)*S)+16)
        else:
            seed,p=self.seed(F(alpha,N),F(i,N),u,v,float(T['Mu'][i,j]))
            d.update(kind='weighted_path',seed=seed,p=p)
        return self.put(key,d,dp)
    def round(self,rnd):
        self.rnd=rnd;self.supportcache={};archive=np.load(HERE/f'{self.prefix}_{rnd}.npz');tab={k:archive[k] for k in archive.files};archive.close();self.tab=tab;self.N=int(tab['N']);N=self.N;self.K=N*10**30
        profs=[]
        for k,start in enumerate([.05,.1,.2,.4,.6,.8]):
            assert tab['outs'][k,-1]<10
            j0=round(start*N);x0=F(j0,N);ini=F(ceilf(self.input.at(x0)*10**30),10**30)+F(1,10**7);z=ini;pts=[(x0,z)];refs=[]
            for i in range(j0+1,N+1):
                j=int(tab['which'][k,i]);assert j>=0
                node=self.node(i,j);dd=self.records[node]
                self.minimum('outer_size',iv(z-decode(dd['v']))[0]);slope=self.cost(i,j)
                self.minimum('outer_blue',IA.add(IA.ri(slope,S),IA.log_rat(S-dd['p'],S))[0])
                z+=F(slope,S*N);pts.append((F(i,N),z));refs.append(node)
            print('EXACT PROFILE',rnd,start,float(z),math.exp(float(z)),flush=True)
            profs.append(Profile(pts));self.profiles.append({'round':rnd,'start':encode(x0),'initial':encode(ini),'N':N,'references':refs,'endpoint':encode(z)})
        for p in profs:self.input=minimum(self.input,p)
        self.input=hull(self.input)
        print('ROUND PASS',rnd,'records',len(self.records),'gamma',float(self.input.at(F(1))),flush=True)
        gc.collect()
    def save(self,out):
        data={'format':'bellman_dag_v1','S':S,'root_artifact_sha256':hashlib.sha256((Path(__file__).resolve().parents[1]/'input_proof.zip').read_bytes()).hexdigest(),'edge_file':Path(str(out)+'.edges.gz').name,'records':self.records,'profiles':self.profiles}
        with gzip.open(str(out)+'.edges.gz','wb',compresslevel=5) as f:f.write(self.edge_array.tobytes())
        with gzip.open(out,'wt',compresslevel=5) as f:json.dump(data,f,separators=(',',':'))
        rep={'status':'GENERATOR_CHECKS_PASS','records':len(self.records),'path_edges':self.edges,'weighted_seeds':self.seed_count,'maximum_dependency_depth':self.maxdepth,'minimum_margins':{k:IA.fmt(v) for k,v in self.mins.items()},'exponent':str(self.input.at(F(1))),'exponent_float':float(self.input.at(F(1))),'base_float':math.exp(float(self.input.at(F(1))))}
        Path(str(out)+'.generation.json').write_text(json.dumps(rep,indent=2));print(rep,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--prefix',default='dual');p.add_argument('--rounds',type=int,default=1);p.add_argument('--output',default='bellman_certificate.json.gz');a=p.parse_args();b=Build(a.prefix)
    for r in range(a.rounds):b.round(r)
    b.save(HERE/a.output)
