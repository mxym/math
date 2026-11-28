"""Independent exact Cartesian replay for two low-LCM exceptions.

Usage: python3 verify_factor_odd_covering_two_exceptions.py data.json
The supplied JSON contains only frozen rational choices, not search code.
"""
from fractions import Fraction as R
from itertools import product
from math import lcm,prod
from pathlib import Path
import sys,json
if not __debug__:
    raise RuntimeError("Run in normal mode, without -O")

PRS=(3,5,7,11,13,17,19,23,29,31,37,41,43)
LIM=473824157932125

def stage_bounds(primes, caps, schedule, omitted=None):
    """Make independent coordinate tables; integrate on Cartesian vectors."""
    n=len(caps)
    flags=(1,1)+tuple(x for x,y in schedule)
    delta=(R(0),R(0))+tuple(R(y,10000) for x,y in schedule)
    assert len(flags)==len(delta)==len(primes)==n
    assert all(d>=0 and d<=R(1,2) for d in delta)
    omit=(0,)*n if omitted is None else tuple(omitted)
    nz=[j for j,e in enumerate(omit) if e]
    k=nz[-1] if nz else -1
    tightened=len(nz)==1 and flags[k]==1
    atom=R(0) if k<0 else R(1,primes[k]**omit[k])
    prev_tables=[]
    prev_den=1
    for j,p in enumerate(primes):
        s=sum((R(1,p**e) for e in range(1,caps[j]+1)),R(0))
        g=R(1)/(1-s+(atom if j==k and tightened else 0)) if flags[j] else R(1)
        c=1/(1-delta[j])
        a=s*g
        basepay=R(-flags[j])*a-delta[j]
        missing=g*atom if j==k and not tightened else R(0)
        denominator=lcm(a.denominator,basepay.denominator,missing.denominator)
        aa,bb,mm=(int(denominator*x) for x in (a,basepay,missing))
        total=0
        if mm:
            demanded=omit[:j]
            for cell in product(*prev_tables):
                xx=prod(e+1 for e,w in cell)
                yy=aa*xx+bb-(mm if all(e>=r for (e,w),r in zip(cell,demanded)) else 0)
                if yy>0:
                    total+=yy*prod(w for e,w in cell)
        else:
            for cell in product(*prev_tables):
                yy=aa*prod(e+1 for e,w in cell)+bb
                if yy>0:
                    total+=yy*prod(w for e,w in cell)
        yield c*R(total,denominator*prev_den)
        # Store integer mass numerators after reducing each coordinate to its
        # own common denominator. This is not the companion's grouped convolution.
        tails=[R(1)]+[c*g/(p**e) for e in range(1,caps[j]+1)]+[R(0)]
        tab=[a-b for a,b in zip(tails,tails[1:])]
        assert sum(tab)==1 and all(v>=0 for v in tab)
        den=lcm(*(v.denominator for v in tab))
        prev_den*=den
        prev_tables.append([(e,int(v*den)) for e,v in enumerate(tab) if v])

def pp(x):
    return -(-x.numerator*1000000//x.denominator)

def value(p,a,s,o=None):
    return sum(stage_bounds(p,a,s,o),R(0))

def initial(r, h):
    return [(1,h),(1,3000),(1,4150),(0,4700),(1,3900)]+[(1,5000)]*(r-7)

def packed_allocate(p, limit):
    budget=(limit-1)//(3*prod(p))
    for m in range(1,budget+1):
        a=[2]+[1]*(len(p)-1)
        rem=m
        for i,q in enumerate(p):
            while rem%q==0:
                rem//=q
                a[i]+=1
        if rem==1:
            assert prod(q**e for q,e in zip(p,a))<limit
            yield tuple(a)

if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit(__doc__)
    data=json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    want={(4,3,2,2,1,1,1,1,1),(5,3,3,1,1,1,1,1,1)}
    assert set(tuple(row["a"]) for row in data)==want
    assert 3*prod(PRS)>=LIM
    reports=[]
    for r in range(9,13):
        p=PRS[:r]
        allcaps=list(packed_allocate(p,LIM))
        bad=set(); ceiling=0
        for a in allcaps:
            f=min(value(p,a,initial(r,h)) for h in (1700,1950))
            if pp(f)>=1000000:
                bad.add(a)
            else:
                assert f<1
                ceiling=max(ceiling,pp(f))
        assert bad==(want if r==9 else set())
        reports.append((len(allcaps),ceiling))
    assert reports==[(1081,998264),(211,993646),(20,843424),(1,561855)]
    print("packed",reports,flush=True)

    shifted=PRS[:8]+(31,)
    special=[(0,3265),(0,3967),(0,4615),(0,4706),(0,4211),(1,5000),(1,5000)]
    r9=[]
    for row in data:
        p,a,forced=row["p"],row["a"],row["forced"]
        assert tuple(p)==PRS[:9]
        L=prod(q**e for q,e in zip(p,a))
        f=min(value(shifted,a,s) for s in (initial(9,1700),initial(9,1950),special))
        seen=set();maximum=0
        for z in forced:
            o=z["exp"];s=z["schedule"]
            assert len(o)==len(a) and any(o) and all(isinstance(k,int) and 0<=k<=b for k,b in zip(o,a))
            v=prod(q**k for q,k in zip(p,o))
            assert v==z["modulus"] and v not in seen
            seen.add(v)
            f2=value(p,a,s,o)
            assert f2<1 and pp(f2)==z["ppm"]
            maximum=max(maximum,pp(f2))
        r9.append((L,pp(f),len(seen),maximum))
    assert r9==[(168131152814625,996519,70,999828),(320977655373375,995453,131,999993)]
    print("actual LCMs, shifted ppm, mandatory count, omission maxima",r9)
    print("PASS independent Cartesian replay")
