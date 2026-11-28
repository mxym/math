#!/usr/bin/env python3
"""Check the affine formula against independent permutations and row operations."""
from itertools import permutations,product

G=list(permutations(range(3)))
ID=G.index((0,1,2))
M=[[G.index(tuple(a[b[i]] for i in range(3))) for b in G] for a in G]
V=[next(j for j in range(6) if M[i][j]==ID)for i in range(6)]
A=[((g[1]-g[0])%3,g[0]) for g in G]
TRAN=[i for i,g in enumerate(G) if all(g[j]!=j for j in range(3))]

def combine(q):
    H=ID
    for t in q:H=M[t][H]
    return H

def compare(l,R):
    X=list(product((0,1),repeat=l))
    cnt=0
    # Deterministically sample all base tables with the first two
    # free base permutations and all changes for representative rigid covers.
    for g0 in product(range(6),repeat=min(l-1,2)):
        g0=g0+(ID,)*(l-1-len(g0))
        g=g0+(V[combine(g0)],)
        for d in product(*(TRAN if i in R else range(6) for i in range(l))):
            h=[(g[i],M[d[i]][g[i]]) for i in range(l)]
            p=[]
            for i in range(l):
                s=combine(g[i+1:])
                p.append(A[M[M[s][d[i]]][V[s]]])
            for x in X:
                left=combine(h[i][x[i]] for i in range(l))==ID
                sign=sum(x[i] for i,(a,b) in enumerate(p) if a==2)
                shift=sum(x[i]*b*(-1)**sum(x[j] for j in range(i+1,l) if p[j][0]==2)
                          for i,(a,b) in enumerate(p))
                assert left==(sign%2==0 and shift%3==0)
                cnt+=1
    return cnt

def rank(A,p):
    A=[list(r) for r in A]
    r=0
    for j in range(len(A[0])):
        nz=next((i for i in range(r,len(A)) if A[i][j]%p),None)
        if nz is None:continue
        A[r],A[nz]=A[nz],A[r]
        piv=pow(A[r][j]%p,-1,p)
        for i in range(r+1,len(A)):
            f=A[i][j]*piv%p
            A[i]=[(a-f*b)%p for a,b in zip(A[i],A[r])]
        r+=1
    return r

counts=[compare(l,R) for l,R in [(3,{1,2}),(4,{1,3}),(5,{0,1,3}),(6,{1,3,5})]]
U=G.index((1,2,0));V0=G.index((0,2,1))
X=list(product((0,1),repeat=6))
D=[x for x in X if combine((U if i%2 else V0) if x[i] else ID
                           for i in range(6))==ID]
assert len(D)==11
F=[x[1::2] for x in D if not any(x[::2])]
H=[x[1::2] for x in D if x[::2]==(1,1,0)]
assert rank(F+H,3)==3
assert any(sum(x)%2 for x in F)
assert not any(all(sum(a*b for a,b in zip(v,x))%3==0 for x in D)
               for v in product(range(3),repeat=6) if v[1] and v[3] and v[5])
print(f"Independent S3 products vs affine coefficients: {sum(counts)} closures evaluated.")
print("Reflection witness: rigid F3 rank 3 certified; all affine-linear substitutes rejected.")
