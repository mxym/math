#!/usr/bin/env python3
"""Synthetic arithmetic checks for fixed-base dyadic ideal stabilization."""
from collections import Counter
from itertools import product
from random import Random


def trim(a, q):
    a = [x%q for x in a]
    while a and not a[-1]:
        a.pop()
    return tuple(a)


def sub(a,b,q):
    return trim([(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))],q)


def rem(a,b,q):
    a = list(trim(a,q))
    c = pow(b[-1],-1,q)
    while len(a)>=len(b):
        s = len(a)-len(b)
        z = a[-1]*c
        for j,t in enumerate(b):
            a[s+j] = (a[s+j]-z*t)%q
        a = list(trim(a,q))
    return tuple(a)


def mul(a,b,q):
    c = [0]*(len(a)+len(b)-1)
    for j,u in enumerate(a):
        for k,v in enumerate(b):
            c[j+k] += u*v
    return trim(c,q)


def power(a,n,f,q):
    r=(1,)
    while n:
        if n&1:
            r=rem(mul(r,a,q),f,q)
        a=rem(mul(a,a,q),f,q)
        n//=2
    return r


def gcd_degree(a,b,p):
    a,b=trim(a,p),trim(b,p)
    while b:
        a,b=b,rem(a,b,p)
    return len(a)-1


def irreducible_pow2(f,p):
    n=len(f)-1
    assert n>=2 and n & (n-1)==0
    x=(0,1)
    h=power(x,p**(n//2),f,p)
    assert gcd_degree(f,sub(h,x,p),p)==0
    assert power(h,p**(n//2),f,p)==x


def substitute(a,k):
    z=[0]*((len(a)-1)*k+1)
    z[::k]=a
    return tuple(z)


def rootpoly(d):
    return (1,)+(0,)*(d-1)+(1,)


def factor_checks():
    count=0
    for p,d0 in ((3,4),(5,4),(7,8),(17,16)):
        base=[]
        for a,b in product(range(p),repeat=2):
            f=(a,b,1)
            if not rem(rootpoly(d0),f,p):
                base.append(f)
        assert 2*len(base)==d0
        for k in (1,2,4,8):
            f=(1,)
            for g in base:
                h=substitute(g,k)
                irreducible_pow2(h,p)
                f=mul(f,h,p)
                count+=1
            assert f==rootpoly(d0*k)
    return count


def two_lifts(p,e,d0,a,b):
    q=p**e
    fs=[(a[0]+p*i,a[1]+p*j,1)
        for i,j in product(range(q//p),repeat=2)]
    gs=[(b[0]+p*i,b[1]+p*j,1)
        for i,j in product(range(q//p),repeat=2)]
    pairs=[(f,g) for f,g in product(fs,gs)
           if mul(f,g,q)==rootpoly(d0)]
    assert len(pairs)==1
    return pairs[0]


def in_ideal(a, factors, e, p):
    q = p**e
    residues=[rem(a,f,q) for f in factors]
    mask=[]
    for j in product(range(e+1),repeat=len(factors)):
        mask.append(all(all(v%p**s == 0 for v in r)
                        for r,s in zip(residues,j)))
    return mask


def lift_checks():
    rng=Random(6217)
    cases=0
    for p,e,d0,a,b in ((3,2,4,(2,1,1),(2,2,1)),
                        (3,3,4,(2,1,1),(2,2,1)),
                        (5,2,4,(2,0,1),(3,0,1))):
        q=p**e
        fs=two_lifts(p,e,d0,a,b)
        for k in (1,2,4):
            gs=tuple(substitute(f,k) for f in fs)
            assert mul(gs[0],gs[1],q)==rootpoly(k*d0)
            for _ in range(350):
                aw=tuple(rng.randrange(q) for j in range(d0*k))
                base=[in_ideal(aw[j::k],fs,e,p) for j in range(k)]
                both=[all(col) for col in zip(*base)]
                assert in_ideal(aw,gs,e,p)==both
                cases+=1
    return cases


def fiber_checks():
    rng=Random(166)
    rows=0
    for q in (3,5,9,15):
        for d in (2,3):
            for _ in range(100):
                a,b=[[rng.randrange(q) for j in range(d)] for k in range(2)]
                group={tuple((i*x+j*y)%q for x,y in zip(a,b))
                       for i,j in product(range(q),repeat=2)}
                n=1
                prefixes={()}
                for i in range(1,d+1):
                    projections={x[:i] for x in group}
                    count=Counter(x[:-1] for x in projections)
                    assert set(count)==prefixes
                    fibers=set(count.values())
                    assert len(fibers)==1
                    k=fibers.pop()
                    assert q%k==0
                    n*=k
                    prefixes=projections
                assert len(group)==n
                rows+=1
    return rows


if __name__=="__main__":
    print("PASS stable finite-field factors:",factor_checks())
    print("PASS lifted component ideal checks:",lift_checks())
    print("PASS additive subgroup projection fibers:",fiber_checks())
