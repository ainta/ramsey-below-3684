"""Outward repairs: keep search slopes, enlarge exponents only when necessary."""
from build_certificate import *
PADS=10**10

def node(self,i,j):
    from build_fast import trace_path
    cached=int(self.record_ids[i,j])
    if cached>=0:return cached
    key=(self.rnd,i,j);T=self.tab;N=self.N;nom=self.ratv(i,j);aidx=int(T['A'][i,j]);co=self.cost(i,j)
    assert T['R'][i,j]>0 and aidx!=0
    d={'ratio':encode(F(i,N)),'cost':co};pad=0
    def finish(kind,p,dep=0):
        d.update(kind=kind,p=p,v=encode(nom+F(pad,PADS)),padding=pad)
        return self.put(key,d,dep)
    if aidx==-1:
        # A larger exponent is sufficient for the established input itself.
        e=self.evalues[i]
        if nom<=e:pad=max(0,ceilf((e-nom+F(1,10**9))*PADS))
        self.minimum('input_margin',iv(nom+F(pad,PADS)-e)[0])
        return finish('input',math.ceil(math.exp(-15.)*S)+16)
    alpha=aidx if aidx>0 else -aidx-2;assert 1<=alpha<=i
    cols,ok=trace_path(i,j,alpha,N,T['Z'],T['Cost'],T['FC'],T['req'],T['ids'],T['length']);assert ok
    rows=np.arange(i,alpha,-1,dtype=np.int32);refs=self.record_ids[rows,cols]
    for k in np.flatnonzero(refs<0):
        if self.record_ids[rows[k],cols[k]]<0:self.node(int(rows[k]),int(cols[k]))
    refs=self.record_ids[rows,cols];assert np.all(refs>=0)
    slopes=np.ceil(T['Cost'][rows,cols]*S).astype(np.int64);total=int(slopes.sum());unom=nom-F(1,10**8)-F(total,S*N)
    dp=int(np.max(np.frombuffer(self.rd,dtype=np.int32)[refs]))+1 if len(refs) else 0
    pad=int(np.max(np.frombuffer(self.rpad,dtype=np.int64)[refs])) if len(refs) else 0
    if aidx<0:
        e=self.evalues[alpha];base={'kind':'input'}
        # Prefer a previously proved unconditional starting state when helpful.
        cand=np.flatnonzero((T['A'][alpha]<0)&(T['R'][alpha]>14.)&(T['Z'][alpha]<float(unom)))
        if len(cand):
            jj=int(cand[0]);child=self.node(alpha,jj)
            if self.rkind[child]:
                cv=self.ratv(alpha,jj)+F(self.rpad[child],PADS)
                if cv<e:e=cv;base={'kind':'record','child':child};dp=max(dp,self.rd[child]+1)
        pad=max(pad,ceilf((e-unom+F(1,10**9))*PADS));pad=max(pad,0)
        u=unom+F(pad,PADS);self.minimum('unconditional_start',iv(u-e)[0]);d['base']=base
        kind='unconditional_path';p=math.ceil(math.exp(-15.)*S)+16
    else:
        step=1;became_unconditional=False
        for attempt in range(40):
            v=nom+F(pad,PADS);u=unom+F(pad,PADS)
            if v>self.evalues[i]+F(1,10**9):
                self.minimum('input_margin',iv(v-self.evalues[i])[0])
                return finish('input',math.ceil(math.exp(-15.)*S)+16)
            if u>self.evalues[alpha]+F(1,10**9):
                d['base']={'kind':'input'};p=math.ceil(math.exp(-15.)*S)+16;became_unconditional=True
                self.minimum('unconditional_start',iv(u-self.evalues[alpha])[0]);break
            seed,p=self.seed(F(alpha,N),F(i,N),u,v,float(T['Mu'][i,j]))
            blue=co/S+math.log1p(-p/S)
            if blue>1e-9:break
            self.seed_count-=1;pad+=step;step*=2
        else:raise AssertionError(('unable to repair',key))
        if became_unconditional:kind='unconditional_path'
        else:d['seed']=seed;kind='weighted_path'
    offset=self.edges;self.edges+=len(refs)
    self.edgefile.write(cols.astype('<u2').tobytes() if getattr(self,'columns',False) else refs.astype('<u4').tobytes())
    d.update(start=encode(F(alpha,N)),path=[offset,len(refs)],end_gap=encode(F(1,10**8)))
    return finish(kind,p,dp)

def round_(self,rnd,filename=None):
    self.rnd=rnd;self.supportcache={};archive=np.load(filename or HERE/f'{self.prefix}_{rnd}.npz');self.tab={k:archive[k] for k in archive.files};archive.close();T=self.tab;self.N=N=int(T['N']);self.K=N*10**30
    self.record_ids=np.full(T['Z'].shape,-1,np.int32);profs=[]
    self.evalues=[None]+[self.input.at(F(i,N)) for i in range(1,N+1)]
    for k,start in enumerate([.05,.1,.2,.4,.6,.8]):
        assert T['outs'][k,-1]<10
        j0=round(start*N);x0=F(j0,N);refs=[];cum=F(0);required=F(0);maxpad=0
        for i in range(j0+1,N+1):
            j=int(T['which'][k,i]);assert j>=0;ci=self.node(i,j);refs.append(ci)
            v=self.ratv(i,j)+F(self.rpad[ci],PADS);required=max(required,v-cum);cum+=F(self.cost(i,j),S*N);maxpad=max(maxpad,self.rpad[ci])
        original=F(str(float(np.interp(float(x0),T['ts'],T['zs']))))+F(1,10**7)
        ini=max(self.input.at(x0)+F(1,10**7),required+F(1,10**9),original+F(maxpad,PADS));ini=F(ceilf(ini*10**30),10**30);z=ini;pts=[(x0,z)]
        for i,ci in enumerate(refs,j0+1):
            j=int(T['which'][k,i]);self.minimum('outer_size',iv(z-self.ratv(i,j)-F(self.rpad[ci],PADS))[0]);slope=self.cost(i,j)
            self.minimum('outer_blue',IA.add(IA.ri(slope,S),IA.log_rat(S-self.rp[ci],S))[0]);z+=F(slope,S*N);pts.append((F(i,N),z))
        print('EXACT PROFILE',rnd,start,float(z),math.exp(float(z)),'padding',maxpad/PADS,flush=True)
        profs.append(Profile(pts));self.profiles.append({'round':rnd,'start':encode(x0),'initial':encode(ini),'N':N,'references':refs,'endpoint':encode(z)})
    for p in profs:self.input=minimum(self.input,p)
    self.input=hull(self.input);self.recordfile.flush();self.edgefile.flush()
    print('ROUND PASS',rnd,'records',self.count,'gamma',float(self.input.at(F(1))),flush=True)
    Path(str(self.out)+'.checkpoint.json').write_text(json.dumps({'round':rnd,'records':self.count,'edges':self.edges,'profiles':self.profiles,'input':[[encode(t),encode(z)] for t,z in self.input.p]}));gc.collect()

def fast_seed(self,alpha,end,u,v,mu):
    """Discovery-only reconstruction. The independent verifier checks all of it."""
    ts=self.tab['ts'];zs=self.tab['zs'];af=float(alpha);tf=float(end);uf=float(u);vf=float(v)
    D=uf+af*math.log(mu);C=-math.log1p(-mu);tau=(C-D)/(tf*C);tt=min(tau,1/tau)
    assert D>0 and tau>0
    tt=max(tt,ts[0])
    j=max(0,min(np.searchsorted(ts,tt,side='right')-1,len(ts)-2))
    sl=(zs[j+1]-zs[j])/(ts[j+1]-ts[j]);value=zs[j]+sl*(tt-ts[j]);aa=sl if tau<=1 else value-tt*sl
    ai=round(aa*S);pad=100
    if ai not in self.supportcache:
        self.supportcache[ai]=ceilf(self.input.seed_b(F(ai-pad,S))*S)+pad
        aw=IA.ri(ai-pad,S);assert aw[0]>self.A0[1] and aw[1]<self.Up0[0]
    bi=self.supportcache[ai];mi=round(mu*S);mm=mi/S;a=ai/S;b=bi/S
    dd=uf+af*math.log(mm);thi=math.ceil((a+tf*b-vf+2e-10)/dd*S);assert thi>0
    rho=(1-mm)*(a+thi/S*math.log1p(-mm));assert rho>0
    pi=math.ceil(math.exp(-rho)*S)+24;p0=pi+24;assert 0<pi<p0<S
    self.seed_count+=1
    return [ai,bi,thi,mi,pi],p0
