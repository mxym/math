#!/usr/bin/env python3
"""Independent rank/support checks and exact conditional erasure calculations."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb, log2, prod, sqrt

def count_rank(m,k,j):
    return (prod((2**m-2**i)*(2**k-2**i) for i in range(j))
            // prod(2**j-2**i for i in range(j)))

def theory(m,k):
    return sum(Q(count_rank(m,k,j),1<<(m*k))*(1-Q(1<<j,1<<m))
               for j in range(min(m,k)+1))

def image(cols):
    support={0}
    for x in cols:
        support|={x^y for y in support}
    return support

cases=0
for m in range(1,5):
    M=1<<m
    for k in range(5):
        N=1<<k
        hist=Counter(len(image(cols)) for cols in product(range(M),repeat=k))
        assert hist=={1<<j:count_rank(m,k,j) for j in range(min(m,k)+1)}
        B=sum(Q(n,M**k)*(1-Q(s,M)) for s,n in hist.items())
        assert B==theory(m,k)
        lead=Q(M-1,2*N)
        assert lead-Q((M-1)*(M-2),8*N*N)<=B<=min(Q(1),lead)
        l=Q(M-1,2*N+M-2)
        assert Q(1,4)*min(1,Q(M,N))<=l<=B
        # Direct count of annihilating linear forms on every support.
        f1=f2=0
        for s,h in hist.items():
            j=M//s
            f1+=h*(j-1)
            f2+=h*(j-1)*(j-2)
        assert Q(f1,M**k)==Q(M-1,N)
        assert Q(f2,M**k)==Q((M-1)*(M-2),N*N)
        cases+=1
print(f"exact rectangular support histograms, constants and annihilator moments: {cases} PASS")

# Explicit average for overlapping conditional support sets, not inferred
# from the rank formula. Each item is (conditional probability, points).
sides=[
    (Q(1,4),(0,1,2,3)),
    (Q(1,3),(1,6)),
    (Q(1,6),(0,3,5,6)),
    (Q(1,4),(5,)),
]
assert sum(p for p,_ in sides)==1
for m in range(1,4):
    M=1<<m
    total=0
    for cols in product(range(M),repeat=3):
        def hash0(x):
            z=0
            for i,c in enumerate(cols):
                if x>>i&1:z^=c
            return z
        for p,points in sides:
            nn=len(points)
            c=Counter(hash0(x) for x in points)
            total+=p*sum(abs(Q(c[z],nn)-Q(1,M)) for z in range(M))/2
    assert total/M**3==sum(p*theory(m,len(pts).bit_length()-1) for p,pts in sides)
print("overlapping affine conditioning, direct strong total variation: 3 PASS")

cases=0
for eta,n,m in product((Q(1,8),Q(1,2),Q(3,4)),range(1,5),(1,2)):
    M=1<<m
    # Average the error of each individual hash over erasure sets.
    # Revealed bit values and the affine output offset do not alter TV.
    direct=0
    for cols in product(range(M),repeat=n):
        for mask in range(1<<n):
            ic=[z for i,z in enumerate(cols) if mask>>i&1]
            k=len(ic)
            direct+=eta**k*(1-eta)**(n-k)*(1-Q(len(image(ic)),M))
    direct/=M**n
    ave=sum(comb(n,k)*eta**k*(1-eta)**(n-k)*theory(m,k) for k in range(n+1))
    clipped=sum(comb(n,k)*eta**k*(1-eta)**(n-k)*min(1,Q(M,1<<k))
                for k in range(n+1))
    assert direct==ave and clipped/4<=ave<=clipped
    cases+=1
print(f"exact BEC conditional-rank and clipped tails: {cases} PASS")

def dual(eta,R,cap):
    # The tilted mean is strictly decreasing for 0<eta<1.
    m=lambda th: (eta*2**(-th))/(1-eta+eta*2**(-th))
    l,h=0.,cap
    for _ in range(60):
        t=(l+h)/2
        if m(t)>R:l=t
        else:h=t
    t=(l+h)/2
    return -t*R-log2(1-eta+eta*2**(-t))

# Numerically compare closed-form dual and direct Bernoulli type variational
# minimization. The exact analytical calculation is in the proof.
checks=0
for eta in (.125,.5,.75):
    critical=eta/(sqrt(2)*(1-eta)+eta)
    def rel(s):
        return ((s*log2(s/eta) if s else 0) +
                ((1-s)*log2((1-s)/(1-eta)) if s<1 else 0))
    for R in (critical/2,critical,(critical+eta)/2,eta,eta+.1):
        v=dual(eta,R,1)
        u=dual(eta,R,.5)
        grid=[i/2048 for i in range(2049)]+[R] if R<=1 else [i/2048 for i in range(2049)]
        direct=min(rel(s)+max(0,s-R) for s in grid)
        assert -1e-14<=direct-v<1e-5
        assert u<=v+1e-14
        if R<critical: assert u<v-1e-6
        checks+=1
print(f"tilted-mean exponent vs type rate; strict three/four gap: {checks} PASS")
