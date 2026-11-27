#!/usr/bin/env python3
"""Independent exact audit of mxym/math 8c18b45b54d27ac69886527cf7030ce0c5a63d41.
Needs NumPy; no external files. The 1743 range avoids assuming either the
40/60 small-order multiplicity classification or the 15*sqrt(N) row bound.
For the alternative cutoff, count at most 300 roots of order dividing 60
by Vandermonde, each multiplicity <=5. For remaining counts r_i the
saturation indices below give r_i*r_j<=4*N (the listed zero planes have
incompatible phases), hence sum <= max(20 sqrt(N),N/2+72) by choosing
the largest r_i<=N/2 and breaking at 2 sqrt(N). Compare to (2)-(3).
In the finite search, literal primitive-order residue pairs populate each
phase table. Ramanujan's integer trace of the squared logarithmic
derivatives measures the multiplicities at small orders.
"""
if not __debug__:raise RuntimeError("enable assertions")
from itertools import combinations
from fractions import Fraction as F
from math import gcd,lcm
PAIRS=(
    ((1,0,0),(0,-1,1)), ((1,0,0),(1,-1,-1)),
    ((1,-2,0),(0,0,1)), ((1,-2,0),(1,0,-1)),
    ((1,0,-2),(0,1,0)), ((1,0,-2),(1,-1,0)),
    ((0,1,0),(0,0,1)), ((0,1,0),(1,0,-1)),
    ((1,-1,0),(0,0,1)), ((1,-1,0),(1,0,-1)),
)
def cross(x,y):return tuple(x[(i+1)%3]*y[(i+2)%3]-x[(i+2)%3]*y[(i+1)%3] for i in range(3))
def product(x,y):return sum(a*b for a,b in zip(x,y))
def minors(rows):return gcd(*(v for x,y in combinations(rows,2) for v in cross(x,y)))
for e in [1,-1]:
    V=[(1,0,0),(1,0,F(1,2)),(1,F(1,2),F(1,2)) if e==1 else (1,F(1,4),F(1,4))]
    values=[];bad=[]
    for (i,(a,b)),(j,(c,d)) in combinations(enumerate(PAIRS),2):
        X=cross(cross(a,b),cross(c,d));H=tuple(int(w//gcd(*X)) for w in X)
        # Smith indices of rank-2 row lattices before/after adjoining primitive H
        m=lcm(minors([a,b])//minors([a,b,H]),minors([c,d])//minors([c,d,H]))
        idx=gcd(*(product(x,cross(y,z))for x,y,z in combinations((a,b,c,d),3)))
        h=[product(v,H) for v in V]
        const=(1+(i>=6))*(1+(j>=6))*idx*m*max(map(abs,h))
        values.append(const)
        if min(h)<0<max(h):bad.append((i,j))
    assert max(values)==4
    assert bad==([(1,2),(1,4),(2,4),(2,7),(3,6),(4,8)] if e==1 else [(3,6)])
n=1744;assert (73*n-32900)>50*n+7200 and (73*n-32900)**2>2000**2*n and 4*n*73**2>2000**2
print('independent rank-2 saturation-index / coarse N<1744 cutoff PASS')
from math import gcd
import numpy as np
from itertools import product
M=1743
phi=list(range(6*M+1))
for i in range(2,len(phi)):
    if phi[i]==i:
        for j in range(i,len(phi),i): phi[j]-=phi[j]//i
mu60=[m for m in range(1,61) if 60%m==0]
tab={(typ,sa,sb):np.zeros((M+1,M+1),dtype=np.int32) for typ in [2,3] for sa,sb in product([1,-1],repeat=2)}
for m in range(1,6*M+1):
    if 60%m==0:continue
    for (typ,sa,sb),v in tab.items():
        phases=[(0,0)] if typ==2 else [(2,4),(4,2)] # in sixths of a turn
        for a,b in phases:
            a=(a+(3 if sa<0 else 0))%6*m;b=(b+(3 if sb<0 else 0))%6*m
            if a%6 or b%6:continue
            v[a//6::m,b//6::m]+=phi[m]
def mob(n):return 1 if n==1 else -sum(mob(d) for d in range(1,n) if n%d==0)
ram={m:[sum(d*mob(m//d)for d in range(1,m+1) if gcd(j,m)%d==0)for j in range(m)] for m in mu60}
# squared magnitudes over primitive conjugates, integers, not literal complex root checks
def insmall(n,s,t,e):
    z=[n,0,n-s,s,n-t,t];A=[1,e,-1,-e,-1,-e]
    count=0
    for m in mu60:
        r=ram[m]; B=[r[(z[i]-z[j])%m]*(2 if i!=j else 1) for i in range(6) for j in range(i+1)]
        pairs=[(i,j)for i in range(6)for j in range(i+1)]
        coeff=A[:]
        for deriv in range(6):
            q=sum(u*coeff[i]*coeff[j] for u,(i,j) in zip(B,pairs))
            assert q>=0
            if q:break
            count+=phi[m]
            coeff=[x*y for x,y in zip(coeff,z)]
        else:raise ArithmeticError()
    return count
for e,exp in [(1,(8908829,410,0)),(-1,(4708172,16382,0))]:
    res=[0]*3
    # Direct Ramanujan test for every residue triple modulo 60.
    nn,ss,tt=np.indices((60,60,60))
    Z=[nn,0,nn-ss,ss,nn-tt,tt]; signs=[1,e,-1,-e,-1,-e]
    small=np.zeros((60,60,60),dtype=np.int16)
    for m in mu60:
        V=np.full((60,60,60),6*phi[m],dtype=np.int32);row=np.array(ram[m])
        for j in range(6):
            for i in range(j):V+=2*signs[i]*signs[j]*row[(Z[i]-Z[j])%m]
        assert V.min()>=0
        small+=(V==0)*phi[m]
    assert small.max()<=60
    for n in range(260 if e==1 else 56,M+1):
        v=100**(7*n);w=1024*101**(7*n);lo=26;hi=1+n//2
        while lo+1<hi:
            j=(lo+hi)//2
            if 27**j*v<=16**j*w:lo=j
            else:hi=j
        dmax=2+2*lo if lo>=27 else 0
        if not dmax:continue
        s,t=np.array(np.triu_indices(n//2))+1
        good=np.gcd(np.gcd(s,t),n)==1
        if e==-1:good&=2*(s+t)<n
        s,t=s[good],t[good]
        res[0]+=len(s)
        P=lambda a,b,sa,sb:tab[2,sa,sb][a,b]
        T=lambda a,b,sa,sb:tab[3,sa,sb][a,b]
        y=n-2*s;z=n-2*t
        outside=P(n,t-s,-e,-1)+P(n,n-s-t,-e,-e)+P(y,t,-e,1)+P(y,n-t,-e,e)+P(z,s,-e,1)+P(z,n-s,-e,e)+T(s,t,-1,-1)+T(s,n-t,-1,-e)+T(n-s,t,-e,-1)+T(n-s,n-t,-e,-e)
        idx=np.where(5*small[n%60,s%60,t%60]+outside>=n-dmax)[0];res[1]+=len(idx)
        for j in idx:
            actual=insmall(n,int(s[j]),int(t[j]),e)
            assert actual<=5*small[n%60,int(s[j])%60,int(t[j])%60]
            if actual+outside[j]>=n-dmax:res[2]+=1
    print('independent primitive-order table / Ramanujan audit',e,res,flush=True)
    assert tuple(res)==((183224481,101,0) if e==1 else (91667042,2728,0))