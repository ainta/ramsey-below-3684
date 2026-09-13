"""Floating-point discovery only; not a proof. Requires numpy and numba."""
import numpy as np
from numba import njit

@njit
def eval_profile(ts,zs,t):
    j=np.searchsorted(ts,t,side="right")-1
    j=max(0,min(j,len(ts)-2))
    slope=(zs[j+1]-zs[j])/(ts[j+1]-ts[j])
    return zs[j]+slope*(t-ts[j])

@njit
def gain(mu,lam,z,ts,zs):
    d=z+lam*np.log(mu)
    L=np.log1p(-mu)
    tau=(d+L)/(lam*L)
    if d<=0 or tau<=0:
        return -1e100
    t=min(tau,1/tau)
    if t<ts[0]:
        return -1e100
    value=max(tau,1.)*eval_profile(ts,zs,t)
    old_gain=(1-mu)*(-L)/d*(z-lam*value)
    return old_gain

@njit
def optimize(lam,z,ts,zs):
    mu0=np.exp(-z/lam)
    grid=np.empty(61)
    vals=np.empty(61)
    for j in range(61):
        mu=mu0+(1-mu0)*(1e-7+(1-2e-7)*j/60)
        grid[j]=mu
        vals[j]=gain(mu,lam,z,ts,zs)
    best=-1e100
    gr=(np.sqrt(5.)-1)/2
    for bj in range(61):
        if bj>0 and vals[bj]<vals[bj-1]:
            continue
        if bj<60 and vals[bj]<vals[bj+1]:
            continue
        lo=grid[max(0,bj-1)]
        hi=grid[min(60,bj+1)]
        x1=hi-gr*(hi-lo)
        x2=lo+gr*(hi-lo)
        f1=gain(x1,lam,z,ts,zs)
        f2=gain(x2,lam,z,ts,zs)
        for _ in range(35):
            if f1>f2:
                hi=x2; x2=x1; f2=f1
                x1=hi-gr*(hi-lo)
                f1=gain(x1,lam,z,ts,zs)
            else:
                lo=x1; x1=x2; f1=f2
                x2=lo+gr*(hi-lo)
                f2=gain(x2,lam,z,ts,zs)
        best=max(best,f1,f2)
    return best

@njit
def update(ts,zs,base):
    out=np.empty(len(ts))
    slopes=np.empty(len(ts)-1)
    out[0]=base
    for j in range(len(ts)-1):
        r=optimize(ts[j],out[j],ts,zs)
        if r<=0:
            raise ValueError("nonpositive candidate gain")
        slope=-np.log(-np.expm1(-r))
        slopes[j]=slope
        out[j+1]=out[j]+slope*(ts[j+1]-ts[j])
    return out,slopes

def U(t):
    return ((1+t)*np.log1p(t)-t*np.log(t)
            +(-t/4+3*t*t/100+2*t*t*t/25)*np.exp(-t))
