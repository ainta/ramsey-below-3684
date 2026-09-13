"""Exact rational profile operations; no numerical optimizer."""
from fractions import Fraction as F
from bisect import bisect_right
from pathlib import Path
import gzip,json
S=10**12;V=2*S**3

def ceilf(x):return -((-x.numerator)//x.denominator)
def encode(x):return [x.numerator,x.denominator]
def decode(x):return F(*x)

class Profile:
    def __init__(self,points):
        self.p=points;self.x=[p[0] for p in points]
        self.sl=[(points[j+1][1]-points[j][1])/(points[j+1][0]-points[j][0]) for j in range(len(points)-1)]
    def at(self,t):
        j=max(0,min(bisect_right(self.x,t)-1,len(self.p)-2))
        return self.p[j][1]+self.sl[j]*(t-self.p[j][0])
    def seed_b(self,a):
        # Requires increasing concavity. Both orientations are maximized.
        lo=0;hi=len(self.p)-1
        while lo<hi:
            j=(lo+hi)//2
            if self.p[j][1]-self.p[j][0]*self.sl[j]<a:lo=j+1
            else:hi=j
        b1=(self.p[lo][1]-a)/self.p[lo][0]
        lo=0;hi=len(self.p)-1
        while lo<hi:
            j=(lo+hi)//2
            if self.sl[j]>a:lo=j+1
            else:hi=j
        b2=self.p[lo][1]-self.p[lo][0]*a
        return max(F(0),b1,b2)
    def check_shape(self):
        assert all(x>0 for x in self.sl)
        assert all(self.sl[j]>=self.sl[j+1] for j in range(len(self.sl)-1))

def minimum(p,q):
    xs=sorted(set(p.x+q.x));out=[]
    for k,t in enumerate(xs):
        yp=p.at(t)
        if t<q.x[0] or t>q.x[-1]:
            out.append((t,yp));continue
        yq=q.at(t)
        if k>0 and xs[k-1]>=q.x[0]:
            t0=xs[k-1];dp=p.at(t0)-q.at(t0);d=yp-yq
            if dp*d<0:
                tc=t0+(t-t0)*dp/(dp-d)
                out.append((tc,p.at(tc)))
        out.append((t,min(yp,yq)))
    return Profile(out)

def hull(p):
    full=p.p+[(1/t,z/t) for t,z in p.p[-2::-1]]
    st=[]
    for pt in full:
        while len(st)>1:
            a,b=st[-2:]
            if (b[1]-a[1])*(pt[0]-b[0])>(pt[1]-b[1])*(b[0]-a[0]):break
            st.pop()
        st.append(pt)
    curve=Profile(st);out=[v for v in st if v[0]<1]+[(F(1),curve.at(F(1)))]
    result=Profile(out);result.check_shape();return result

def root_profile(root):
    root=Path(root)
    data=json.load(gzip.open(root/'ramsey_candidate_continuation_release/certificate.json.gz','rt'))
    row=data['rounds'][-1];xs=row.get('knots',data['knots']);vs=[data['initial_value']]
    for j,s in enumerate(row['slopes']):vs.append(vs[-1]+2*S*s*(xs[j+1]-xs[j]))
    inds=row['majorant_indices'];prev=Profile([(F(xs[j],S),F(vs[j],V)) for j in inds]);del data,row
    data=json.load(gzip.open(root/'certificate.json.gz','rt'));xs=data['knots'];vs=[data['initial_value']]
    for j,s in enumerate(data['slopes']):vs.append(vs[-1]+2*S*s*(xs[j+1]-xs[j]))
    out=Profile([(F(x,S),F(v,V)) for x,v in zip(xs,vs)])
    return hull(minimum(prev,out))
