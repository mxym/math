#!/usr/bin/env python3
"""Exact, small certificates used in FactorLengthSixSalemClassification.md."""
from fractions import Fraction as F
from functools import reduce
from itertools import combinations, product
from math import gcd, lcm

if not __debug__:
    raise RuntimeError("Run without -O")


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])


def primitive(x):
    d=reduce(gcd,x)
    assert d
    y=tuple(a//d for a in x)
    return y if next(a for a in y if a)>0 else tuple(-a for a in y)


def divisors(n):
    return [d for d in range(1,n+1) if not n%d]


def divide_exact(f,g):
    f=list(f)
    k=len(g)-1
    q=[0]*(len(f)-k)
    for j in range(len(q)-1,-1,-1):
        q[j]=f[j+k]
        for i,x in enumerate(g):
            f[j+i]-=q[j]*x
    assert not any(f)
    return q


def cyclotomic_tables():
    phi,rows={},{}
    for m in divisors(60):
        f=[-1]+[0]*(m-1)+[1]
        for d in divisors(m)[:-1]:
            f=divide_exact(f,phi[d])
        phi[m]=f
        k=len(f)-1
        z=[1]+[0]*(k-1)
        r=[tuple(z)]
        for _ in range(1,m):
            a=z[-1]
            z=[u-a*v for u,v in zip([0]+z[:-1],f)]
            r.append(tuple(z))
        rows[m]=r
    return rows


def feasible_double(rows,e):
    # Df(zeta)=0 is a homogeneous linear system in (N,s,t).
    if not rows:
        return True,None
    if len(rows)==1:
        # N=4 scaling of the closure of each two-gap range. If the
        # zero section is a face, its barycentre detects the strict
        # inequalities s>0 and, in the minus case, 2(s+t)<N.
        corners=((4,0,0),(4,0,2),(4,2,2) if e==1 else (4,1,1))
        h=[dot(rows[0],v) for v in corners]
        if min(h)<0<max(h):
            return True,None
        face=[v for v,y in zip(corners,h) if y==0]
        if not face:
            return False,None
        n,s,t=map(sum,zip(*face))
        return s>0 and (e==1 or 2*(s+t)<n),None
    a,b=rows[:2]
    w=cross(a,b)
    assert any(w)
    if w[0]<0:
        w=tuple(-x for x in w)
    n,s,t=w
    ok=n>0 and 0<s<=t and 2*t<=n and (e==1 or 2*(s+t)<n)
    if not ok or any(dot(a,w) for a in rows):
        return False,None
    # A line meeting the cone has only one primitive integer ray vector.
    return True,primitive(w)


def check_exceptional():
    R=cyclotomic_tables()
    for e,expected in ((1,(32,40)),(-1,(60,60))):
        parts={}
        for m,W in R.items():
            for n in range(m):
                for s in range(m):
                    for t in range(m):
                        a,b,c,d,f,g=[W[x%m] for x in (n,0,n-s,s,n-t,t)]
                        if any(w+e*x-y-e*z-u-e*v for w,x,y,z,u,v in zip(a,b,c,d,f,g)):
                            continue
                        coef=set()
                        for row in zip((x-y-z for x,y,z in zip(a,c,f)),
                                       (x-e*y for x,y in zip(c,d)),
                                       (x-e*y for x,y in zip(f,g))):
                            if any(row):
                                coef.add(primitive(row))
                        parts[m,n,s,t]=feasible_double(sorted(coef),e)
        largest_simple=largest_with_mult=primitive_residues=0
        for n,s,t in product(range(60),repeat=3):
            if gcd(n,s,t,60)!=1:
                continue
            primitive_residues+=1
            T=U=0
            for m,W in R.items():
                x=parts.get((m,n%m,s%m,t%m))
                if x is None:
                    continue
                d=len(W[0])
                T+=d
                U+=d
                feasible,ray=x
                if feasible and (ray is None or tuple(u%60 for u in ray)==(n,s,t)):
                    U+=4*d
            largest_simple=max(T,largest_simple)
            largest_with_mult=max(U,largest_with_mult)
        got=(largest_simple,largest_with_mult)
        assert got==expected,(e,got)
        print("orders dividing 60:",e,primitive_residues,"simple/all",*got,flush=True)


# Integer coefficient rows for the ten pairs of phase exponents.
PAIRS=(
    ((1,0,0),(0,-1,1)), ((1,0,0),(1,-1,-1)),
    ((1,-2,0),(0,0,1)), ((1,-2,0),(1,0,-1)),
    ((1,0,-2),(0,1,0)), ((1,0,-2),(1,-1,0)),
    ((0,1,0),(0,0,1)), ((0,1,0),(1,0,-1)),
    ((1,-1,0),(0,0,1)), ((1,-1,0),(1,0,-1)),
)


def denominator(a,b,h):
    # Rational coefficients of h in the basis a,b.
    for i,j in combinations(range(3),2):
        d=a[i]*b[j]-a[j]*b[i]
        if d:
            x=F(h[i]*b[j]-h[j]*b[i],d)
            y=F(a[i]*h[j]-a[j]*h[i],d)
            assert all(q==x*r+y*s for q,r,s in zip(h,a,b))
            return lcm(x.denominator,y.denominator)
    raise ValueError("Repeated direction rows")


def check_pairs():
    expected={
       1:[(1,2,(1,-2,-2)),(1,4,(1,-2,-2)),(2,4,(1,-2,-2)),
          (2,7,(1,-2,-1)),(3,6,(0,2,-1)),(4,8,(1,-1,-2))],
      -1:[(3,6,(0,2,-1))],
    }
    for e in (1,-1):
        verts=((1,0,0),(1,0,F(1,2)),
               (1,F(1,2),F(1,2)) if e==1 else (1,F(1,4),F(1,4)))
        C=[[0]*10 for _ in range(10)]
        zeros=[]
        for i,j in combinations(range(10),2):
            a,b=PAIRS[i]
            c,d=PAIRS[j]
            H=primitive(cross(cross(a,b),cross(c,d)))
            idx=gcd(*(dot(w,cross(x,y)) for w,x,y in combinations((a,b,c,d),3)))
            mul=lcm(denominator(a,b,H),denominator(c,d,H))
            v=[dot(H,w) for w in verts]
            if min(v)<0<max(v):
                zeros.append((i,j,H))
            w=(1+(i>=6))*(1+(j>=6))
            C[i][j]=C[j][i]=w*idx*mul*max(map(abs,v))
        assert zeros==expected[e],(e,zeros)
        assert max(map(max,C))==4 and max(map(sum,C))==24
        for row in C:
            for c in row:
                if c:
                    y=c+sum(min(c,x) for x in row)
                    assert y*y<=225*c,(row,c,y)
        print("pair constants:",e,"max",max(map(max,C)),"max row sum",max(map(sum,C)),
              "zero cases",len(zeros),flush=True)


def check_numeric():
    assert 27**27>16**27*1024**2
    assert 27**27*100**1400>16**27*101**1400
    assert 101**518+100**518<14*101**259*100**259
    n=650
    assert 73*n-8900>50*n+4800
    assert (73*n-8900)**2>1500**2*n
    # The increase of 1500 sqrt(N) per real unit is no more than this
    # derivative at 650, which is smaller than 73 by the following check:
    assert 1500**2<4*n*73**2
    print("exact norm and degree comparisons: PASS",flush=True)


if __name__=="__main__":
    check_exceptional()
    check_pairs()
    check_numeric()
