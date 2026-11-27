#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from math import comb

def max_pairwise_multiple(q,n,h):
    strings=list(product(range(q),repeat=n))
    adj=[]
    for a in strings:
        adj.append(sum((sum(x==y for x,y in zip(a,b)) % h == 0 and a!=b)<<i
                       for i,b in enumerate(strings)))
    best=0
    def visit(S,r):
        nonlocal best
        if r>best:
            best=r
        while S and S.bit_count()+r>best:
            nextbit=S & -S
            j=nextbit.bit_length()-1
            S^=nextbit
            visit(S & adj[j],r+1)
    visit((1<<len(strings))-1,0)
    return best

tested=sharp=0
for q,lim in ((2,4),(3,2)):
    for n in range(1,lim+1):
        for h in range(2,n+2):
            m=max_pairwise_multiple(q,n,h)
            if n%h:
                assert m <= 1+n*(q-1)
                tested+=1
                sharp+=m==1+n*(q-1)
print(f"independent maximal-clique search: {tested} tiny nondivisible cases, {sharp} rank-ceiling equalities")

old_candidates=0
for q in range(2,301):
    for h in range(2,q+1):
        if q*(q+1)%h or q%h==0:
            continue
        # n = d+h, computed separately from d's Plotkin equality value.
        n=(h-1)*q+h
        assert n%h and q**3>1+n*(q-1)
        old_candidates+=1
print(f"dimension-three scan q<=300: {old_candidates} weaker-divisibility-only parameters excluded")

# Recover the number of exactly-one-agreement neighbors directly from both moments.
for q in (2,4,7,10,16,34):
    d=q*q
    n=(q+1)*q+2
    gap=n-d
    C=F(comb(n,2)*(q*q-1),comb(gap,2))
    assert C.denominator==1
    assert n*(q**3-1)-gap*C==0
    assert q**4>1+(q-1)*n
    assert (n%gap==0)==(q==2)
print("dimension-four table: exact moment and rank tests on all six rows PASS")

# An exact Gram check on 16 binary affine words using parity characters rather
# than generator columns. Each sign row is a Walsh character or its negative.
signs=[tuple(c*(-1)**((u&x).bit_count()%2) for x in range(8))
       for c in (1,-1) for u in range(8)]
B=[[int(symbol==r[i]) for i in range(8) for symbol in (1,-1)] for r in signs]
G=[[sum(a*b for a,b in zip(row,col)) for col in B] for row in B]
assert all(g==8 if i==j else g in (0,4) for i,row in enumerate(G) for j,g in enumerate(row))
def rank(A):
    A=[list(map(F,row)) for row in A]
    r=0
    for c in range(len(A[0])):
        v=next((i for i in range(r,len(A)) if A[i][c]),None)
        if v is None:
            continue
        A[r],A[v]=A[v],A[r]
        for i in range(r+1,len(A)):
            if A[i][c]:
                f=A[i][c]/A[r][c]
                for j in range(c,len(A[0])):
                    A[i][j]-=f*A[r][j]
        r+=1
    return r
assert rank(G)==9
# For every opposite-sign pair of the same character, every neighbor in
# the agreement-four graph has the same relation to the two rows.
v=[0]*16
v[0]=1
v[1]=-1
v[8]=1
v[9]=-1
A=[[(g-8*(i==j))//4 for j,g in enumerate(row)] for i,row in enumerate(G)]
assert [sum(a*b for a,b in zip(row,v)) for row in G]==[0]*16
assert [sum(a*b for a,b in zip(row,v)) for row in A]==[-2*b for b in v]
print("binary full-weight case: exact rank 9, explicit Gram kernel and adjacency eigenvalue -2 PASS")
