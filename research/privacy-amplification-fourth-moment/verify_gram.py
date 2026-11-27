#!/usr/bin/env python3
"""Exact indicator Gram/PSD checks and a separate numerical two-level clipping check."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import sqrt


def law(m,n,s):
    k,r=divmod(n,4)
    for sample in product(range(m),repeat=3*k+r):
        out=[]
        for j in range(k):
            a,b,c=sample[3*j:3*j+3]
            out.extend((a,b,c,(a+b-c-s)%m))
        yield tuple(out)+sample[3*k:]


def gram(ms,m,n):
    es=list(combinations(range(n),2))
    accum=[[0]*len(es) for _ in es]
    for f in ms:
        for z in range(m):
            x=[m*(y==z)-1 for y in f]
            ps=[x[i]*x[j] for i,j in es]
            for i in range(len(es)):
                for j in range(i,len(es)):
                    accum[i][j]+=ps[i]*ps[j]
    denom=len(ms)*m*(m-1)**2
    return es,[[F(accum[min(i,j)][max(i,j)],denom) for j in range(len(es))]
               for i in range(len(es))]


for m,n in ((2,4),(3,4),(5,4),(3,8),(2,9)):
    for s in (0,1):
        ms=list(law(m,n,s))
        for ids in combinations(range(n),3):
            h=Counter(tuple(f[i] for i in ids) for f in ms)
            assert len(h)==m**3 and set(h.values())=={len(ms)//m**3}
        es,K=gram(ms,m,n)
        coeff=F(1,m-1) if s==0 else -F(1,(m-1)**2)
        for i,e in enumerate(es):
            for j,e2 in enumerate(es):
                support=set(e+e2)
                match=len(support)==4 and len({x//4 for x in support})==1
                assert K[i][j]==(1 if i==j else coeff if match else 0)
        print(f"Z/{m}, inputs={n}, relation={s}: {len(ms)} seeds, pair spectrum edge {1+abs(coeff)}")

# Independent binary-affine input-group calculation, at vector output size 4.
n=8;m=4
def parity(z): return z.bit_count()%2
ms=[tuple((parity(a&x)^c)|((parity(b&x)^d)<<1) for x in range(n))
    for a,b in product(range(n),repeat=2) for c,d in product((0,1),repeat=2)]
es,K=gram(ms,m,n)
for i,(a,b) in enumerate(es):
    for j,(c,d) in enumerate(es):
        assert K[i][j]==(1 if i==j else F(1,3) if a^b==c^d else 0)
assert {sum(row) for row in K}=={F(2)}
print("Binary affine 3->2: all pair-feature Gram entries exact, spectral edge 2")

# Full rectangular representation (independent from occupancy verifier).
I=(F(1),F(0),F(0),F(1))
O=(F(0),)*4
def add(*xs): return tuple(map(sum,zip(*xs))) if xs else O
def scl(c,x): return tuple(c*t for t in x)
def sub(a,b): return add(a,scl(-1,b))
def mul(a,b):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
def psd(x):
    a,b,c,d=x
    return b==c and a>=0 and d>=0 and a*d>=b*c
def norm(x):
    a,b,c,d=x
    return (abs(a+d)+sqrt((a-d)**2+4*b*c))/2
def norm1(x):
    a,b,c,d=x
    return max(abs(a+d),sqrt((a-d)**2+4*b*c))
def tr(x): return x[0]+x[3]
def sq(x): return mul(x,x)
def functional(x,fun):
    a,b,c,d=x
    tr2=(a+d)/2
    sp=sqrt((a-d)**2+4*b*c)
    if sp==0: return scl(fun(tr2),I)
    lo,hi=fun(tr2-sp/2),fun(tr2+sp/2)
    return add(scl((lo+hi)/2,I),scl((hi-lo)/sp,sub(x,scl(tr2,I))))

p=F(1,3);v=p*(1-p)
M=tuple(tuple(F(x,100) for x in mat) for mat in
        ((60,0,0,-35),(0,33,33,0),(26,-10,-10,-18),(18,9,9,28)))
Q=add(*(sq(a) for a in M))
assert psd(sub(scl(1/(4*p),I),Q))
assert any(mul(a,b)!=mul(b,a) for a,b in combinations(M,2))
assert all(psd(add(I,scl(sign,a))) for a in M for sign in (-1,1))
R=tuple(tuple(F(x,100) for x in a) for a in
        ((20,4,4,10),(5,5,5,15),(18,-2,-2,7),(10,1,1,15)))
assert all(psd(a) for a in R) and sum(map(tr,R))==1
assert any(mul(a,b)!=mul(b,a) for a,b in combinations(R,2))
tested=0
for s in (0,1):
    ms=list(law(3,4,s))
    es,K=gram(ms,3,4)
    C=F(3,2) if s==0 else F(5,4)
    D=(1-2*p)**2+(1+2*C)*(1-p)/4
    neq=add()
    H=[O]*4
    clipped=0
    delta=0.0
    c0=float(1-p)*max(3,sqrt(2+4*C))/4
    examples=0
    for f in ms:
        for z in range(3):
            B=[F(f[i]==z)-p for i in range(4)]
            X=add(*(scl(t,a) for t,a in zip(B,M)))
            X4=sq(sq(X))
            neq=add(neq,X4)
            hx=functional(X,lambda t: t-max(-c0,min(c0,t)))
            clipped+=norm(hx)>1e-12
            for i,b in enumerate(B):
                H[i]=add(H[i],scl(b,hx))
            delta+=norm1(add(*(scl(t,a) for t,a in zip(B,R))))/2
            examples+=1
    covs=[add(mul(M[i],M[j]),mul(M[j],M[i])) for i,j in es]
    expected=add(scl(v*v,sq(Q)),scl((1-2*p)**2*v,add(*(sq(sq(x)) for x in M))),
                 scl(v*v,add(*(scl(K[i][j],mul(a,b)) for i,a in enumerate(covs) for j,b in enumerate(covs)))))
    assert scl(F(1,examples),neq)==expected
    assert psd(sub(scl(v*D,Q),expected))
    assert clipped>0
    H=[scl(2/(examples*v),a) for a in H]
    assert all(norm(h)<1 for h in H)
    U=sub(scl(1/(4*p),I),add(*(sq(x) for x in H)))
    assert U[0]>0 and U[3]>0 and abs(U[1]-U[2])<1e-12 and U[0]*U[3]>U[1]*U[2]
    obj=sum(tr(mul(a,b)) for a,b in zip(R,M))
    assert obj>0
    assert delta/len(ms) > obj/max(3,sqrt(2+4*C))
    tested+=examples
    print(f"Noncommuting check s={s}: {examples} bin/seed samples; {clipped} nonzero clipping residuals")
print(f"Exact operator covariance/PSD and numeric clipping checks: PASS, {tested} total samples")
