#!/usr/bin/env python3
"""Verify the quadratic weighted-book finite certificate using ONLY exact integer arithmetic.

No optimizer, floating-point transcendental routine, or third-party library is used.
Logarithms are enclosed by a range-reduced atanh series with an explicit tail bound.
exp(-t), 0 <= t <= 1, is enclosed by alternating Taylor sums.
This checks the finite inequalities, not the combinatorial theorem in proof_note.md and weighted_candidate_lemma.md.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path

if not __debug__:
    raise SystemExit('Verification requires assertions; run Python without -O.')

DECIMAL_PLACES = int(os.environ.get('RAMSEY_INTERVAL_DIGITS', '40'))
assert DECIMAL_PLACES in (18, 40), 'Only the two audited precision modes are supported.'
Q = 10**DECIMAL_PLACES
NLOG = 20 if DECIMAL_PLACES == 18 else 50
# Tail of 2*sum u^(2j+1)/(2j+1), |u| <= 1/3, is less than 1/Q.
assert 9*Q < 4*(2*NLOG+1)*3**(2*NLOG+1)

def ceil_div(a: int, b: int) -> int:
    assert b > 0
    return -((-a)//b)

def ri(n: int, d: int = 1) -> tuple[int,int]:
    assert d > 0
    return n*Q//d, ceil_div(n*Q,d)

def add(x,y): return x[0]+y[0], x[1]+y[1]
def sub(x,y): return x[0]-y[1], x[1]-y[0]
def mul(x,y):
    products=(x[0]*y[0],x[0]*y[1],x[1]*y[0],x[1]*y[1])
    return min(products)//Q,ceil_div(max(products),Q)
def scale(x,k):
    return (x[0]*k,x[1]*k) if k>=0 else (x[1]*k,x[0]*k)
def div_pos_int(x,d):
    assert d>0
    return x[0]//d,ceil_div(x[1],d)

def log_reduced(n,d):
    assert d <= n <= 2*d
    u=ri(n-d,n+d)
    u2=mul(u,u)
    w=u
    lo=hi=0
    for j in range(NLOG):
        term=div_pos_int(w,2*j+1)
        lo+=term[0]
        hi+=term[1]
        w=mul(w,u2)
    return 2*lo,2*hi+1

LOG2=log_reduced(2,1)

def log_rat(n,d=1):
    assert n>0 and d>0
    k=n.bit_length()-d.bit_length()
    if k>=0:
        nn=n; dd=d<<k
    else:
        nn=n<<(-k); dd=d
    if nn<dd:
        k-=1; nn*=2
    elif nn>=2*dd:
        k+=1; dd*=2
    assert dd<=nn<2*dd
    return add(log_reduced(nn,dd),scale(LOG2,k))

def exp_minus_unit(n,d):
    assert 0<=n<=d
    t=ri(n,d)
    w=(Q,Q)
    total=(Q,Q)
    upper=None
    for j in range(1,42):
        w=div_pos_int(mul(w,t),j)
        total=add(total,w) if j%2==0 else sub(total,w)
        if j==40:
            upper=total[1]  # Even Taylor truncation.
    return total[0],upper   # Odd Taylor truncation, then even truncation.

ONE=(Q,Q)

def input_U(n,S):
    t=ri(n,S)
    t2=mul(t,t); t3=mul(t2,t)
    poly=add(add(scale(div_pos_int(t,4),-1),
                 scale(div_pos_int(t2,100),3)),
             scale(div_pos_int(t3,25),2))
    entropy=sub(mul(add(ONE,t),log_rat(S+n,S)),
                mul(t,log_rat(n,S)))
    return add(entropy,mul(poly,exp_minus_unit(n,S)))

def input_Up(n,S):
    t=ri(n,S)
    t2=mul(t,t); t3=mul(t2,t)
    poly=add(add(ri(-1,4),scale(div_pos_int(t,100),31)),
             sub(scale(div_pos_int(t2,100),21),
                 scale(div_pos_int(t3,100),8)))
    return add(log_rat(S+n,n),mul(poly,exp_minus_unit(n,S)))


def div_positive(x,y):
    assert y[0]>0
    pairs=[(a*Q,b) for a in x for b in y]
    return min(a//b for a,b in pairs),max(ceil_div(a,b) for a,b in pairs)

def exact_support_ceil(ai,xs,zs,S,V):
    lo=0;hi=len(xs)-1
    while lo<hi:
        j=(lo+hi)//2;dx=xs[j+1]-xs[j];dz=zs[j+1]-zs[j]
        if S*(zs[j]*dx-xs[j]*dz)<ai*V*dx:lo=j+1
        else:hi=j
    first=ceil_div(S*(zs[lo]*S-ai*V),V*xs[lo])
    lo=0;hi=len(xs)-1
    while lo<hi:
        j=(lo+hi)//2;dx=xs[j+1]-xs[j];dz=zs[j+1]-zs[j]
        if dz*S*S>ai*V*dx:lo=j+1
        else:hi=j
    second=ceil_div(zs[lo]*S*S-xs[lo]*ai*V,V*S)
    return max(0,first,second)

def fmt(v,den=Q,digits=36):
    """Round a rational DOWN to a decimal; formatting also uses only integers."""
    assert den>0 and digits>=0
    n=(v*10**digits)//den
    sign='-' if n<0 else ''
    n=abs(n)
    whole,frac=divmod(n,10**digits)
    return sign+str(whole)+'.'+str(frac).zfill(digits)

def exact_decimal(v,den):
    """Exact decimal for a denominator with no prime factors besides 2 and 5."""
    d=den; twos=fives=0
    while d%2==0:d//=2;twos+=1
    while d%5==0:d//=5;fives+=1
    assert d==1
    return fmt(v,den,max(twos,fives))

def increasing_concave(xs,zs):
    assert len(xs)==len(zs)
    for j in range(len(xs)-1):
        assert zs[j+1]>zs[j],('increasing polygon',j)
        if j+2<len(xs):
            assert ((zs[j+1]-zs[j])*(xs[j+2]-xs[j+1])>=
                    (zs[j+2]-zs[j+1])*(xs[j+1]-xs[j])),('concave polygon',j)

def verify(path,report_path=None,round_start=1,round_end=None):
    data=json.load(gzip.open(path,'rt'))
    assert data['format_version']==3
    assert data['control_columns']==['a','theta','mu0','p_lower','p_upper','slope','curvature']
    S=data['scale'];V=data['value_scale']
    assert S==10**12 and V==2*S**3
    xs=data['knots'];prev=data['input_values'];base=data['output_initial_value'];n=len(xs)-1
    assert len(prev)==n+1 and xs[0]==S//1000 and xs[-1]==S
    assert all(xs[j+1]>xs[j]>0 for j in range(n))
    increasing_concave(xs,prev)
    min_initial=10**100
    for j in range(n+1):
        u=input_U(xs[j],S)
        margin=ri(prev[j],V)[0]-u[1]-ceil_div(Q,10**8)
        assert margin>0,('U knot',j)
        min_initial=min(min_initial,margin)
        if j<n:
            x=xs[j];dx=xs[j+1]-x
            assert (S+2*x)*dx*dx*10**8<8*x*S*S,('U chord error',j)
    u0=input_U(xs[0],S);up0=input_Up(xs[0],S)
    A0=sub(u0,mul(ri(xs[0],S),up0))
    assert ri(base,V)[0]>u0[1]
    print('PASS initial upper profile and endpoint',flush=True)
    entries=[]
    for idx,entry in enumerate(data['rounds'],1):
        rows=entry['controls'];lift=entry['polygon_lift']
        assert len(rows)==n and lift>0
        assert ri(prev[0],V)[0]>u0[1]
        zs=[base];mins=[10**100]*5
        max_chord=0
        for j,row in enumerate(rows):
            ai,thi,mi,pli,phi,si,ki=row
            assert ai>0 and thi>0 and 0<mi<S and 0<pli<phi<S and si>0 and ki>0
            dx=xs[j+1]-xs[j]
            assert ki*dx<S*si,('positive end slope',idx,j)
            assert 4*lift>=ki*dx*dx,('polygon upper approximation',idx,j)
            max_chord=max(max_chord,ceil_div(ki*dx*dx,4))
            zs.append(zs[-1]+2*S*si*dx-ki*dx*dx)
            if not (idx>=round_start and (round_end is None or idx<=round_end)):
                continue
            bi=exact_support_ceil(ai,xs,prev,S,V)
            a,th,m,pl,ph,s,kap,b=[ri(v,S) for v in (ai,thi,mi,pli,phi,si,ki,bi)]
            l=ri(xs[j],S);r=ri(xs[j+1],S);h=ri(dx,S);z=ri(zs[j],V)
            assert a[0]>A0[1] and a[1]<up0[0],('short support window',idx,j)
            one_th=add(ONE,th)
            logm=log_rat(mi,S);log1m=log_rat(S-mi,S)
            H=add(add(a,mul(th,log1m)),th)
            R=mul(sub(ONE,m),sub(H,th))
            assert H[0]>0 and R[0]>0
            lower_density=add(R,log_rat(pli,S))
            upper_density=add(R,log_rat(phi,S))
            blue=add(s,log_rat(S-phi,S))
            budget=add(sub(sub(mul(one_th,z),a),mul(l,b)),mul(mul(th,l),logm))
            assert lower_density[1]<0,('lower density',idx,j,lower_density)
            assert upper_density[0]>0,('upper density',idx,j,upper_density)
            assert blue[0]>0,('initial blue slack',idx,j,blue)
            assert budget[0]>0,('initial budget',idx,j,budget)
            q0=sub(mul(one_th,sub(z,mul(l,s))),a)
            assert q0[1]<0,('q0',idx,j,q0)
            B=add(mul(l,h),div_pos_int(mul(h,h),2))
            qmax=add(q0,mul(mul(one_th,kap),B))
            assert qmax[1]<0,('qmax',idx,j,qmax)
            ml=mul(m,add(ONE,div_positive(mul(q0,h),mul(th,mul(l,l)))))
            assert ml[0]>0,('ml',idx,j)
            v=mul(add(a,th),sub(m,ml))
            assert v[0]>=0 and v[1]<Q,('v',idx,j)
            T=mul(pl,sub(ONE,v))
            assert T[0]>0 and T[1]<Q,('T',idx,j)
            numerator=mul(mul(ml,H),T)
            denominator=mul(mul(th,mul(r,r)),sub(ONE,T))
            C=div_positive(numerator,denominator)
            curvature=sub(scale(kap,-1),mul(C,qmax))
            assert curvature[0]>0,('quadratic supersolution',idx,j,curvature)
            lows=[-lower_density[1],upper_density[0],blue[0],budget[0],curvature[0]]
            mins=[min(v,w) for v,w in zip(mins,lows)]
        prev=[v+lift for v in zs]
        increasing_concave(xs,prev)
        entry_report={'round':idx,'pieces':n,'endpoint_numerator':str(zs[-1]),'endpoint_denominator':str(V),
                      'endpoint_decimal_exact':exact_decimal(zs[-1],V),
                      'polygon_lift':exact_decimal(lift,V),
                      'checked':idx>=round_start and (round_end is None or idx<=round_end)}
        if entry_report['checked']:
            for name,mn in zip(['lower_density_slack','upper_density_slack','blue_slack','budget_slack','curvature_slack'],mins):
                entry_report[name+'_lower']=fmt(mn)
            print('PASS round',idx,'endpoint',entry_report['endpoint_decimal_exact'],flush=True)
        entries.append(entry_report)
        if report_path:
            Path(str(report_path)+'.checkpoint').write_text(json.dumps(entries,indent=2))
    num=data['target_base_numerator'];den=data['target_base_denominator']
    gap=log_rat(num,den)[0]-ri(zs[-1],V)[1]
    assert gap>0,('final base',gap)
    result={'status':'PASS' if round_start==1 and (round_end is None or round_end>=len(entries)) else 'PARTIAL_ROUND_CHECK_PASS',
            'arithmetic':'Python integers with outward-rounded rational intervals; no floating-point arithmetic or optimizer',
            'certificate_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),
            'initial_node_margin_lower':fmt(min_initial),
            'rounds':entries,'target_base_exact':str(num)+'/'+str(den),
            'endpoint_gap_lower':fmt(gap),
            'scope':'Finite continuum certificate only; depends on the separately written weighted candidate lemma and profile argument. Not Lean-formalized.'}
    if report_path:Path(report_path).write_text(json.dumps(result,indent=2)+'\n')
    print('PASS endpoint comparison; scope',result['status'],flush=True)
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',nargs='?',default=str(Path(__file__).with_name('certificate.json.gz')))
    ap.add_argument('--report',default=str(Path(__file__).with_name('reproduced_verification_report.json')))
    ap.add_argument('--round-start',type=int,default=1)
    ap.add_argument('--round-end',type=int,default=None)
    args=ap.parse_args();verify(args.certificate,args.report,args.round_start,args.round_end)
