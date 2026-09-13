"""Exploratory floating-point Bellman sweep. Not a certificate."""
from pathlib import Path
import sys, math, json, gzip, time
import numpy as np
from numba import njit
# Local adaptation: explicit inputs supplied by probe.py. No missing predecessor
# archive, saved verification receipt, or unchecked profile is a default premise.
S=10**12
V=2*S**3
from weighted_numerics import eval_profile,U
from path_opt import path_opt

@njit(cache=True)
def rect_g(mu,alpha,beta,u,v,ts,zs):
    D=u+alpha*np.log(mu); C=-np.log1p(-mu)
    if D<=0:return -1e90
    tau=(C-D)/(beta*C)
    if tau<=0:return -1e90
    t=min(tau,1/tau)
    if t<ts[0] or t>1:return -1e90
    H=max(1.,tau)*eval_profile(ts,zs,t)
    return (1-mu)*C/D*(v-beta*H)

@njit(cache=True)
def rect_opt(alpha,beta,u,v,ts,zs):
    m0=np.exp(-u/alpha)
    if m0>=1:return -1e90,0.
    K=24; gg=np.empty(K+1); mm=np.empty(K+1)
    for j in range(K+1):
        m=m0+(1-m0)*(1e-7+(1-2e-7)*j/K)
        mm[j]=m;gg[j]=rect_g(m,alpha,beta,u,v,ts,zs)
    best=-1e90;bm=0.;gr=.6180339887498949
    for j in range(K+1):
        if j>0 and gg[j]<gg[j-1]:continue
        if j<K and gg[j]<gg[j+1]:continue
        lo=mm[max(0,j-1)];hi=mm[min(K,j+1)]
        m1=hi-gr*(hi-lo);m2=lo+gr*(hi-lo)
        g1=rect_g(m1,alpha,beta,u,v,ts,zs);g2=rect_g(m2,alpha,beta,u,v,ts,zs)
        for k in range(22):
            if g1>g2:
                hi=m2;m2=m1;g2=g1;m1=hi-gr*(hi-lo);g1=rect_g(m1,alpha,beta,u,v,ts,zs)
            else:
                lo=m1;m1=m2;g1=g2;m2=lo+gr*(hi-lo);g2=rect_g(m2,alpha,beta,u,v,ts,zs)
        if g1>best:best=g1;bm=m1
        if g2>best:best=g2;bm=m2
    return best,bm

@njit(cache=True)
def lookup(row,ur,reqs,costs,ids,length):
    lo=0;hi=length
    while lo<hi:
        mid=(lo+hi)//2
        if reqs[row,mid]<ur:lo=mid+1
        else:hi=mid
    if lo==0:return -1,0.
    j=lo-1
    return ids[row,j],costs[row,j]

@njit(cache=True)
def insert(row,j,req,cost,reqs,costs,ids,ln):
    pos=np.searchsorted(reqs[row,:ln],req)
    # Keep undominated requirements / costs. Costs strictly decrease with req.
    if pos>0 and costs[row,pos-1]<=cost:return ln
    end=pos
    while end<ln and costs[row,end]>=cost:end+=1
    nnew=ln-(end-pos)+1
    # overlapping copying explicit
    if end==pos:
        for a in range(ln,pos,-1):
            reqs[row,a]=reqs[row,a-1];costs[row,a]=costs[row,a-1];ids[row,a]=ids[row,a-1]
    else:
        for a in range(end,ln):
            dest=pos+1+a-end
            reqs[row,dest]=reqs[row,a];costs[row,dest]=costs[row,a];ids[row,dest]=ids[row,a]
    reqs[row,pos]=req;costs[row,pos]=cost;ids[row,pos]=j
    return nnew

@njit(cache=True)
def sweep(N,deficits,ts,zs,alpha_stride=1):
    M=len(deficits)+1;h=1./N
    Z=np.zeros((N+1,M));R=np.full((N+1,M),-1e90);Cost=np.full((N+1,M),1e90)
    A=np.zeros((N+1,M),np.int32);Mu=np.zeros((N+1,M));FC=np.full((N+1,M),-1,np.int32)
    startu=np.zeros((N+1,M))
    req=np.full((N+1,M+1),1e90);co=req.copy();ids=np.full((N+1,M+1),-1,np.int32);length=np.zeros(N+1,np.int32)
    depth=np.zeros((N+1,M),np.int32)
    uncond=np.full(N+1,1e90)
    path_u=np.zeros(N+1);path_dep=np.zeros(N+1,np.int32)
    for i in range(1,N+1):
        t=i*h;et=eval_profile(ts,zs,t)
        uncond[i]=et
        for j in range(M):
            z=et-t*deficits[j] if j<M-1 else et+1e-6
            Z[i,j]=z
            if z<=1e-8:continue
            if j==M-1 or z>uncond[i]+2e-8:
                R[i,j]=15.;Cost[i,j]=-np.log1p(-np.exp(-15.))+1e-7;A[i,j]=-1
            else:
                ur=z-1e-8
                path_u[i]=ur;path_dep[i]=0;first=i
                bg=-1e90;bm=0.;bi=i;bu=ur;bdepth=0
                fc=-1;pathdepth=0
                for r in range(i,1,-1):
                    ci,c=lookup(r,ur,req,co,ids,length[r])
                    if ci<0:break
                    if r==i:fc=ci
                    pathdepth=max(pathdepth,depth[r,ci])
                    ur-=h*c
                    if ur<=1e-8:break
                    path_u[r-1]=ur;path_dep[r-1]=pathdepth;first=r-1
                    if ur>uncond[r-1]+2e-8:
                        bg=15.;bi=-(r-1)-2;bu=ur;bm=0.;bdepth=pathdepth+1
                        uncond[i]=min(uncond[i],z)
                        break
                if bg<0:
                    bg,bm,bi=path_opt(t,z,path_u,first,i,N,ts,zs)
                    bu=path_u[bi];bdepth=path_dep[bi]+1 if bi<i else 0
                if bg<=0:continue
                R[i,j]=bg;Cost[i,j]=-np.log1p(-np.exp(-bg))+1e-7
                A[i,j]=bi;Mu[i,j]=bm;FC[i,j]=fc;startu[i,j]=bu;depth[i,j]=bdepth
            length[i]=insert(i,j,Z[i,j]+h*Cost[i,j]+1e-8,Cost[i,j],req,co,ids,length[i])
    return Z,R,Cost,A,Mu,FC,startu,depth,req,co,ids,length

@njit(cache=True)
def forward(N,Z,R,Cost,ts,zs,start):
    h=1./N;F=np.full(N+1,1e90);which=np.full(N+1,-1,np.int32)
    j0=max(1,int(round(start*N)));F[j0]=eval_profile(ts,zs,j0/N)+1e-7
    for i in range(j0+1,N+1):
        best=1e90;bj=-1
        for j in range(Z.shape[1]):
            if Z[i,j]+1e-8<F[i-1] and Cost[i,j]<best:
                best=Cost[i,j];bj=j
        if bj<0:break
        F[i]=F[i-1]+h*best;which[i]=bj
    return F,which

def initial(kind='latest'):
    # Float hull used for discovery; exact support to be checked separately.
    if kind=='U':
        ts=np.unique(np.r_[np.geomspace(.001,.05,500),np.linspace(.05,1,4001)])
        zs=U(ts)+1e-7
    else:
        raise ValueError('Only the GNNW U input is available here; use probe.py for explicit diagnostic inputs')
    return hull(ts,zs)

def hull(ts,zs):
    # Symmetric homogeneous upper concave hull; split at 1.
    xx=np.r_[ts,1/ts[-2::-1]];yy=np.r_[zs,zs[-2::-1]/ts[-2::-1]]
    st=[]
    for j in range(len(xx)):
        while len(st)>1:
            a,b=st[-2:]
            if (yy[b]-yy[a])*(xx[j]-xx[b])>(yy[j]-yy[b])*(xx[b]-xx[a])+1e-16:break
            st.pop()
        st.append(j)
    xs=xx[st];ys=yy[st]
    ts0=np.unique(np.r_[xs[xs<1],1.]);return ts0,np.interp(ts0,xs,ys)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--N',type=int,default=150);p.add_argument('--M',type=int,default=90);p.add_argument('--input',default='latest');p.add_argument('--rounds',type=int,default=3);p.add_argument('--stride',type=int,default=2);p.add_argument('--name',default='trial');a=p.parse_args()
    ts,zs=initial(a.input)
    defs=np.linspace(0,1,a.M)**1.7*.8;defs=defs[::-1]
    for rnd in range(a.rounds):
        print('START',rnd,'input',zs[-1],math.exp(zs[-1]),'knots',len(ts),flush=True);st=time.time()
        arrays=sweep(a.N,defs,ts,zs,a.stride);Z,R,Cost,A,Mu,FC,su,depth,req,co,ids,ln=arrays
        print('SWEEP seconds',time.time()-st,'maxdepth',depth.max(),flush=True)
        for target in [3.6984,3.68,3.65,3.6,3.55]:
            z=math.log(target);jj=np.flatnonzero(Z[-1]<z);best=max(R[-1,jj]) if len(jj) else -1
            print('D(1)',target,'gain',best,'margin',best-math.log(2),flush=True)
        newts=ts.copy();newzs=zs.copy()
        outs=[];wh=[]
        for start in [.05,.1,.2,.4,.6,.8]:
            F,W=forward(a.N,Z,R,Cost,ts,zs,start);outs.append(F);wh.append(W)
            print('OUTER',start,F[-1],math.exp(F[-1]) if F[-1]<10 else -1,flush=True)
            j0=max(1,round(start*a.N));xs=np.arange(j0,a.N+1)/a.N
            if F[-1]>10:continue
            tt=np.unique(np.r_[newts,xs]);vv=np.interp(tt,newts,newzs);mask=tt>=xs[0]
            vv[mask]=np.minimum(vv[mask],np.interp(tt[mask],xs,F[j0:]));newts,newzs=tt,vv
        fn=Path(__file__).parent/f'{a.name}_{rnd}.npz'
        np.savez_compressed(fn,ts=ts,zs=zs,N=a.N,deficits=defs,Z=Z,R=R,Cost=Cost,A=A,Mu=Mu,FC=FC,startu=su,depth=depth,req=req,co=co,ids=ids,length=ln,outs=np.array(outs),which=np.array(wh))
        ts,zs=hull(newts,newzs)
        print('END',rnd,'best',zs[-1],math.exp(zs[-1]),'time',time.time()-st,flush=True)
