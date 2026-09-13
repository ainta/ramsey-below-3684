import numpy as np
from numba import njit
from weighted_numerics import eval_profile
@njit(cache=True)
def path_hull(first,last,us,N):
    hh=np.zeros(last-first+1,np.int32);n=0
    for j in range(first,last+1):
        while n>1:
            a=hh[n-2];b=hh[n-1]
            if (us[b]-us[a])*(j-b) > (us[j]-us[b])*(b-a)+1e-17:break
            n-=1
        hh[n]=j;n+=1
    return hh[:n]
@njit(cache=True)
def path_gain(mu,t,z,us,hh,N,ts,zs):
    lm=np.log(mu);lo=0;hi=len(hh)-1
    while lo<hi:
        j=(lo+hi)//2;aa=hh[j];bb=hh[j+1]
        if us[bb]-us[aa]+(bb-aa)/N*lm>0:lo=j+1
        else:hi=j
    ix=hh[lo];D=us[ix]+ix/N*lm;C=-np.log1p(-mu)
    if D<=0:return -1e90,ix
    tau=(C-D)/(t*C)
    if tau<=0:return -1e90,ix
    r=min(tau,1/tau)
    if r<ts[0]:return -1e90,ix
    H=max(1.,tau)*eval_profile(ts,zs,r)
    return (1-mu)*C/D*(z-t*H),ix
@njit(cache=True)
def path_opt(t,z,us,first,last,N,ts,zs):
    hh=path_hull(first,last,us,N)
    K=40;gg=np.empty(K+1);mm=np.empty(K+1)
    ratio=0.
    for j in range(first,last+1):ratio=max(ratio,us[j]*N/j)
    m0=np.exp(-ratio)
    for j in range(K+1):
        m=m0+(1-m0)*(1e-7+(1-2e-7)*j/K)
        mm[j]=m;gg[j]=path_gain(m,t,z,us,hh,N,ts,zs)[0]
    bg=-1e90;bm=0.;bi=last;gr=.6180339887498949
    for j in range(K+1):
        if j>0 and gg[j]<gg[j-1]:continue
        if j<K and gg[j]<gg[j+1]:continue
        lo=mm[max(0,j-1)];hi=mm[min(K,j+1)]
        m1=hi-gr*(hi-lo);m2=lo+gr*(hi-lo)
        g1,i1=path_gain(m1,t,z,us,hh,N,ts,zs);g2,i2=path_gain(m2,t,z,us,hh,N,ts,zs)
        for q in range(30):
            if g1>g2:
                hi=m2;m2=m1;g2=g1;i2=i1;m1=hi-gr*(hi-lo);g1,i1=path_gain(m1,t,z,us,hh,N,ts,zs)
            else:
                lo=m1;m1=m2;g1=g2;i1=i2;m2=lo+gr*(hi-lo);g2,i2=path_gain(m2,t,z,us,hh,N,ts,zs)
        if g1>bg:bg=g1;bm=m1;bi=i1
        if g2>bg:bg=g2;bm=m2;bi=i2
    return bg,bm,bi
