#!/usr/bin/env python3
"""Exact rational/combinatorial checks for StableRoommatesParityAsymptotics.md."""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import factorial, prod
from random import Random

def parts(n,lo):
    if n==0:
        yield ()
    else:
        for i in range(lo,n+1):
            for rest in parts(n-i,i):yield (i,)+rest
def cyclic_count(p):
    return Q(1,prod(x**j*factorial(j) for x,j in Counter(p).items()))
def df(k):return prod(range(k,0,-2))

# All graph types of long cycles on up to 29 vertices, including odd cycles.
graphs=0
for m in range(30):
    for p in parts(m,3):
        edges=[];nxt=0
        for j in p:
            edges.extend((nxt+i,nxt+(i+1)%j) for i in range(j))
            nxt+=j
        assert len(edges)==m
        assert sum(bool(set(e)&set(f)) for e,f in combinations(edges,2))==m
        graphs+=1

# Integer normalization for both even and unrestricted parity of the active vertices.
weights=0
for N in range(1,81):
    for m in range(N%2,N+1,2):
        x=Q(factorial(N)*df(N-m-1),factorial(N-m)*df(N+m-1))
        y=prod(Q(N-m+2*j,N+j) for j in range(1,m+1))
        assert x==y and 0<x<=1
        if N%2==0:
            assert x==prod(Q(N-2*j,N+2*j+1) for j in range(m//2))
        weights+=1

# Compare signed cycle counts against recurrences and explicit power series.
def e_coeff(m):
    if m<0:return Q(0)
    return sum(Q((-1)**(m-2*j),factorial(m-2*j)*factorial(j)*2**j)
               for j in range(m//2+1))
d=[Q(1),Q(0)]
for k in range(1,31):
    d.append((k*d[k]-d[k-1]/2)/(k+1))
for k in range(32):
    val=sum(cyclic_count(tuple(2*x for x in p))*(-1)**len(p) for p in parts(k,2))
    assert d[k]==val
    if k>=2:assert val<0
for m in range(33):
    a=sum(cyclic_count(p)*(-1)**sum(x%2==0 for x in p) for p in parts(m,3))
    w=sum(cyclic_count(p) for p in parts(m,3))
    assert a==e_coeff(m)+e_coeff(m-1)
    assert 0<=w<=1
assert Q(9,8)*Q(8,3)-5==-2

# Direct moment integration under the even reference probability.
moments=0
for N in range(4,45,2):
    for m in range(0,N+1,2):
        L=N+m;alpha=[2]*m+[1]*(N-m)
        def moment(indices):
            return Q(prod(prod(range(alpha[i],alpha[i]+j)) for i,j in Counter(indices).items()),
                     prod(L+2*j+1 for j in range(len(indices)//2)))
        B=[(i,i+1) for i in range(m,N,2)]
        eq=sum(moment((i,i)) for i in range(N))
        eq2=sum(moment((i,i,j,j)) for i in range(N) for j in range(N))
        eh=sum(moment(x) for x in B)
        eh2=sum(moment(x+y) for x in B for y in B)
        assert eq==Q(2*N+4*m,L+1)
        assert eq2==Q((2*N+4*m)**2+20*N+64*m,(L+1)*(L+3))
        assert eh==Q(len(B),L+1)
        assert eh2==Q(len(B)**2+3*len(B),(L+1)*(L+3))
        assert eh-Q(1,2)-(eq-2)/2==Q(1-4*m,2*(L+1))
        if m>=4:
            den=(L+1)*(L+3)
            assert moment((0,1))==Q(4,L+1)
            assert moment((0,1,0,1))==Q(36,den)
            assert moment((0,1,0,2))==Q(24,den)
            assert moment((0,1,2,3))==Q(16,den)
        moments+=1

# Small exact stability integrals from all retained edge subsets, with
# the singleton multiplier integrated individually in each coordinate.
def integral(p,singleton):
    N=sum(p);degs=[0]*N;removed=set();start=0
    for l in p:
        for i in range(l):
            a,b=start+i,start+(i+1)%l
            removed.add(tuple(sorted((a,b))))
            degs[a]=int(l>2)
        start+=l
    edges=[e for e in combinations(range(N),2) if e not in removed]
    def go(j):
        if j==len(edges):
            return Q(1,prod((a+1)*(a+2 if singleton else 1) for a in degs))
        a,b=edges[j]
        without=go(j+1)
        degs[a]+=1;degs[b]+=1;with_=go(j+1);degs[a]-=1;degs[b]-=1
        return without-with_
    return go(0)
def exact(n):
    b=n%2;N=n-b
    return (N+1 if b else 1)*sum(factorial(N)*cyclic_count(p)*
              (-1)**sum(x>2 for x in p)*integral(p,b)
              for p in parts(N,2) if all(x%2==0 for x in p))
for n,p in {2:Q(1),3:Q(3,4),4:Q(26,27),5:Q(4075,6912),
            6:Q(181431847,194400000),7:Q(246462083,518400000)}.items():
    assert exact(n)==p

# Independently evaluate the pointwise signed identity after restricting
# to the invariant odd-cycle layer, for complete preferences.
def cycle_data(p):
    n=len(p);vis=set();cy=[]
    for i in range(n):
        if i in vis:continue
        c=[];j=i
        while j not in vis:
            c.append(j);vis.add(j);j=p[j]
        assert j==i
        cy.append(tuple(c))
    return cy
def permutations_data(n):
    for p in permutations(range(n)):
        c=cycle_data(p)
        if sum(len(c0)==1 for c0 in c)>1:continue
        o=tuple(c0 for c0 in c if len(c0)%2)
        s=(-1)**sum(len(c0)>=4 and len(c0)%2==0 for c0 in c)
        yield p,tuple(p.index(i) for i in range(n)),o,s
def pointwise(ranks,perm):
    C=Counter();seen=set()
    for p,inv,odd,s in perm:
        if any(row[j]>row[k] for row,j,k in zip(ranks,inv,p)):continue
        base=[ranks[i][p[i]] for i in range(len(p))]
        if any(ranks[i][j]<base[i] and ranks[j][i]<base[j] for i,j in combinations(range(len(p)),2)):
            continue
        C[odd]+=s;seen.add(odd)
    assert len(seen)==1
    odd=next(iter(seen))
    assert C[odd]==1
    return odd
def ranked(piv,order):
    p=list(order)+[piv]
    return tuple(p.index(i) for i in range(len(p)))
rng=Random(471630)
samples=0;count=0
for n in [4,5,6,7]:
    rows=[list(permutations(j for j in range(n) if j!=i)) for i in range(n)]
    perm=tuple(permutations_data(n))
    arr=product(*rows) if n==4 else ([rng.choice(row) for row in rows] for _ in range(120))
    for p in arr:
        odd=pointwise([ranked(i,r) for i,r in enumerate(p)],perm)
        if n==4:count+=not odd
        samples+=1
assert Q(count,6**4)==Q(26,27)
print(f"PASS: {graphs} cycle types; {weights} exact normalizations; {moments} moment cases; "
      f"6 Mertens rational probabilities; {samples} invariant odd-layer exact tests.")
