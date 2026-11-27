#!/usr/bin/env python3
"""Independent exact-rational raw-bin CQ verification using spectral inertia."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import prod


def add(A,B):
    return tuple(tuple(a+b for a,b in zip(ar,br)) for ar,br in zip(A,B))


def scale(c,A):
    return tuple(tuple(c*a for a in row) for row in A)


def tensor(A,B):
    return tuple(tuple(a*b for a in ar for b in br) for ar in A for br in B)


def mul(A,B):
    return tuple(tuple(sum(a*b for a,b in zip(ar,bc)) for bc in zip(*B)) for ar in A)


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def positive_count(A,t):
    """Exact number of eigenvalues strictly above t, by congruence."""
    B=[list(row) for row in A]
    for i in range(len(B)): B[i][i]-=t
    npos=0
    while B:
        dim=len(B)
        diag=next((i for i in range(dim) if B[i][i]),None)
        if diag is not None:
            d=B[diag][diag]
            npos+=d>0
            live=[i for i in range(dim) if i!=diag]
            B=[[B[i][j]-B[i][diag]*B[diag][j]/d for j in live] for i in live]
        else:
            off=next(((i,j) for i in range(dim) for j in range(i+1,dim) if B[i][j]),None)
            if off is None: break
            a,b=off;d=B[a][b];npos+=1
            live=[i for i in range(dim) if i not in off]
            B=[[B[i][j]-(B[i][a]*B[b][j]+B[i][b]*B[a][j])/d for j in live] for i in live]
    return npos


@lru_cache(maxsize=None)
def norm_interval(A):
    dim=len(A); rad=max(sum(map(abs,row)) for row in A)
    if not rad: return F(0),F(0)
    obs=[(i,A[i][i]) for i in range(dim)]
    if all(A[i][j]==0 for i in range(dim) for j in range(i+1,dim)):
        v=sum(abs(a) for _,a in obs)
        return v,v
    lo_sum=hi_sum=F(0)
    for j in range(1,dim+1):
        lo=-rad; hi=rad
        while hi-lo>F(1,1<<22):
            mid=(lo+hi)/2
            if positive_count(A,mid)>=j: lo=mid
            else: hi=mid
        if lo>=0: lo_a,hi_a=lo,hi
        elif hi<=0: lo_a,hi_a=-hi,-lo
        else: lo_a,hi_a=F(0),max(-lo,hi)
        lo_sum+=lo_a;hi_sum+=hi_a
    return lo_sum,hi_sum


def zeromat(m):
    return tuple((F(0),)*m for i in range(m))


def code(A,x):
    return sum((((a&x).bit_count()&1)<<i) for i,a in enumerate(A))


def image(A,u):
    a=0
    for i,x in enumerate(A):
        if u>>i&1: a^=x
    return a


def qprod(m,n,x,R):
    U=((F(1),),)
    for i in range(n): U=tensor(U,R[(x>>(i*m))&((1<<m)-1)])
    return U


def strong_cq(name,k,n,r,R,S):
    N=1<<(k*n)
    M=1<<r
    q=1<<k
    Z=zeromat(len(R[0]))
    assert all(positive_count(a,F(0))<=len(a) and
               positive_count(scale(-1,a),F(0))==0 for a in R)
    assert sum(map(trace,R))==1
    assert any(mul(a,b)!=mul(b,a) for a in R for b in R)
    for j in range(q):
        B=Z
        for x,a in enumerate(R): B=add(B,scale((-1)**((x&j).bit_count()&1),a))
        lo,hi=norm_interval(B)
        assert lo<=S[j]<=hi
    weights=[prod(S[(a>>(j*k))&(q-1)] for j in range(n)) for a in range(N)]
    raw=[qprod(k,n,x,R) for x in range(N)]
    z=zeromat(len(raw[0]));sigma=z
    for a in raw: sigma=add(sigma,a)
    assert trace(sigma)==1
    ideal=scale(-F(1,M),sigma)
    sumlo=sumhi=full_lo=full_hi=F(0);mxs=full=0
    for A in product(range(N),repeat=r):
        O=[z]*M
        for x,st in enumerate(raw):
            key=code(A,x)
            O[key]=add(O[key],st)
        d=[norm_interval(add(b,ideal)) for b in O]
        a,b=(sum(y[i] for y in d)/2 for i in (0,1))
        ww=[weights[image(A,u)] for u in range(1,M)]
        assert max(ww)/2<=b and sum(ww)/2>=a
        for u in range(1,M):
            H=z
            for out,bucket in enumerate(O):
                H=add(H,scale((-1)**((u&out).bit_count()&1),bucket))
            low,high=norm_interval(H)
            assert low<=ww[u-1]<=high
        sumlo+=a;sumhi+=b;mxs+=1
        if all(image(A,u)!=0 for u in range(1,M)):
            full_lo+=a;full_hi+=b;full+=1
    U=F(M-1,2)*F(sum(S),q)**n
    assert sumlo/mxs<=U
    if r==1: assert sumlo/mxs<=U<=sumhi/mxs
    if k==1 and r<=n:
        uf=F(M-1,2*(N-1))*((1+S[1])**n-1)
        assert full>0 and full_lo/full<=uf
        if r==1: assert full_lo/full<=uf<=full_hi/full
    print(f"{name}: k={k} n={n} r={r}, {mxs} matrices ({full} full rank), exact inertia and all parity norms pass")


def matrix(raw,den):
    return ((F(raw[0],den),F(raw[1],den)),(F(raw[1],den),F(raw[2],den)))


# Binary nonuniform mixed, genuinely noncommuting, s=1/5.
R=tuple(matrix(a,40) for a in ((14,3,10),(6,3,10)))
for n,r in ((1,1),(2,1),(2,2),(3,1)):
    strong_cq("Nonuniform mixed CQ",1,n,r,R,(F(1),F(1,5)))

# Hayashi phase-state weights (9/10,1/10), s=3/5; all entries rational.
H=tuple(matrix(a,20) for a in ((9,3,1),(9,-3,1)))
for n,r in ((1,1),(2,1),(2,2),(3,2)):
    strong_cq("Hayashi phase-state source",1,n,r,H,(F(1),F(3,5)))

# Genuine four-input noncommuting example with three nonzero frequencies.
S4=[]
for x in range(4):
    v0=(-1)**(x&1)
    v1=(-1)**(x>>1)
    z=3*v0+v0*v1
    S4.append(matrix((10+z,2*v1,10-z),80))
strong_cq("Four-symbol mixed CQ",2,1,2,tuple(S4),tuple(map(F,(1,"3/10","1/5","1/10"))))

# Exact, integer-only witnesses for the rate threshold and positivity
# in the arXiv v6 Lemma 39 counterexample.
assert 3**300*5**500>2**1608
assert 8**100<2**99*5**100
# At n=100, quotient dimension one: this upper bound is an equality.
D=F(8,5)**100
upper=(D-1)/(2**100-1)
assert upper < D/(2**100) < F(1,2**31)
print("Hayashi v6 example: exact integer rate/positivity certificates; n=100 one-output full-rank bound < 2^-31")
