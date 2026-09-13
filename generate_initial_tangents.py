"""Find and exactly recheck short tangent witnesses for all initial lines.

Floating point selects only a rational witness. Every acceptance test below
uses directed integer arithmetic; the generated Lean data is still untrusted.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
os.environ['RAMSEY_INTERVAL_DIGITS']='18'
import interval_arithmetic as I

def scaled(interval,n,d):return I.div_pos_int(I.scale(interval,n),d)

def value_slope(n,d):
    t=I.ri(n,d)
    term=I.ONE
    total=(0,0)
    for j in range(20):
        total=I.add(total,I.scale(term,1 if j%2==0 else -1))
        term=I.div_pos_int(I.mul(term,t),j+1)
    exponential=total[0]-1,total[1]+1
    poly=-25*n*d*d+3*n*n*d+8*n*n*n
    dp=-25*d**3+31*n*d*d+21*n*n*d-8*n**3
    val=I.add(I.sub(scaled(I.log_rat(d+n,d),d+n,d),scaled(I.log_rat(n,d),n,d)),
              scaled(exponential,poly,100*d**3))
    slope=I.add(I.log_rat(d+n,n),scaled(exponential,dp,100*d**3))
    return val,slope

def derivative(t):
    return math.log((1+t)/t)+math.exp(-t)*(-.25+.31*t+.21*t*t-.08*t*t*t)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('certificates/quantized/initial_tangents.json'))
    args=parser.parse_args()
    source=Path('certificates/quantized/initial_u.json')
    raw=source.read_bytes()
    points=[(Fraction(*t),Fraction(*v)) for t,v in json.loads(raw)['points']]
    witnesses=[]
    minimum=None
    for index,((x0,v0),(x1,v1)) in enumerate(zip(points,points[1:])):
        b=(v1-v0)/(x1-x0)
        a=v0-x0*b
        assert a>0 and b>0
        left,right=1e-12,1.0
        for _ in range(60):
            mid=(left+right)/2
            if derivative(mid)>float(b):left=mid
            else:right=mid
        n,d=round((left+right)/2*10**12),10**12
        assert 0<n<=d
        val,slope=value_slope(n,d)
        at_zero=I.sub(val,scaled(slope,n,d))
        at_one=I.add(val,scaled(slope,d-n,d))
        aa=I.ri(a.numerator,a.denominator)
        bb=I.ri(b.numerator,b.denominator)
        margin=min(aa[0]-at_zero[1],I.add(aa,bb)[0]-at_one[1])
        assert margin>=0,(index,'tangent does not fit',margin)
        minimum=margin if minimum is None else min(minimum,margin)
        witnesses.append([n,d,a.numerator,a.denominator,b.numerator,b.denominator])
        if (index+1)%2000==0:print('EXACT TANGENT',index+1,flush=True)
    result=dict(status='EXACT_TANGENT_WITNESSES_NOT_YET_LEAN',
                source_sha256=hashlib.sha256(raw).hexdigest(),interval_scale=I.Q,
                minimum_margin=minimum,entries=witnesses)
    if args.output.exists() and json.loads(args.output.read_text())!=result:
        raise SystemExit('Refusing to overwrite different witness data')
    args.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS',len(witnesses),'exact tangent witnesses; margin',minimum,'/',I.Q,flush=True)

if __name__=='__main__':main()
