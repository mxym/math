#!/usr/bin/env python3
"""Exact review aids. No claim that finite tests prove the graphon theorem."""
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
from collections import Counter
from itertools import combinations

def check(x,why):
    if not x: raise ValueError(why)

def p2(a):
    return Q(2)**a
C=lambda j: 33*2**j
M=2**3850; delta=p2(-2706); kappa=p2(-598); p0=Q(1,4); tau=p2(-20)
check(1+2/p0**2==33,"density floor")
check(C(132)+2*C(66)<=p2(140) and C(8)<=p2(14),"rooted fluctuations")
check(33*delta<=p2(-675)**4 and p2(-675)<=p0,"small operator")
check(2*p0**3*tau==p2(-25) and (2**7)**2*tau==(p0/2)**2,"variance split")
check(p0**286*p2(-25)-p2(-675+70+7)==kappa,"bridge gain")
check(M*kappa>=2*C(67),"Bernoulli margin")
check((23-1)*13//2==143 and p0**(4*143)*(1+M*delta)>=1,"far case")
check(C(67)<2**73 and C(71)+C(67)<2**78 and Q(3,4)**-4<4,"sparse coefficients")
check(2**73+4*2**78<2**81 and 4*M-4>=680 and p2(81-680)==kappa/2,"sparse margin")
# Self-contained fixed source data: Table 1 of
# github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/
# preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/
# build/sections/complex.tex (blob 178b0e9da21867a727ea847dae8e537b9d719a70).
# Never silently skip the graph check when the earlier note is not installed.
faces = (
 (0,1,3),(0,1,9),(0,2,3),(0,2,9),(1,3,10),(1,7,10),(1,7,12),
 (1,9,12),(2,3,4),(2,4,9),(3,4,11),(3,10,11),(4,8,9),(4,8,11),
 (5,6,7),(5,6,11),(5,7,10),(5,10,11),(6,7,12),(6,8,11),
 (6,8,12),(8,9,12),
)
check(len(set(faces))==22 and all(tuple(sorted(set(f)))==f and len(f)==3 for f in faces),"simple triples")
check(sha256(bytes(i for f in faces for i in f)).hexdigest()=="15dbcae4b12585e40e6766011506a9d8a99fb788b5c4003f0318fb516f0d9778","exact labelled Table 1 fingerprint")
pnts=set().union(*map(set,faces))
check(pnts==set(range(13)),"point set")
adj=[set() for _ in range(len(pnts)+len(faces))]
for j,f in enumerate(faces,start=13):
    for i in f: adj[i].add(j); adj[j].add(i)
seen={0}; stack=[0]
while stack:
    u=stack.pop()
    for v in adj[u]-seen: seen.add(v);stack.append(v)
e0=sum(map(len,adj))//2;v0=len(adj)
check((v0,e0,len(seen))==(35,66,35),"connected H incidence graph")
check([j for j,f in enumerate(faces) if {0,1}<=set(f)]==[0,1],"rooted square")
counts=Counter(t for f in faces for t in combinations(f,2))
check(len(counts)==33 and set(counts.values())=={2},"two faces per used pair")
check(v0+1+3*M==36+3*M and e0+1+4*M==67+4*M,"decorated graph cardinalities")
print("H: source table, 35 vertices, 66 incidences, connectivity and designated square passed.")
print("Explicit scales and connected count: passed (integer M has",len(str(M)),"decimal digits).")
# Verify exact rooted codegree identities and lower bounds for K_{3,2} and K_{4,3}
# on every symmetric two-atom kernel on a four-point value grid, under two measures.
grid=(Q(0),Q(1,3),Q(2,3),Q(1))
count=0
for u,v,w in product(grid,repeat=3):
    W=((u,v),(v,w))
    for t in (Q(1,2),Q(1,5)):
        pi=(t,1-t)
        avg=lambda f:sum(pi[i]*f(i) for i in range(2))
        d=[avg(lambda y:W[x][y]) for x in range(2)]
        p=avg(lambda x:d[x]);z=[r-p for r in d]
        K=[[avg(lambda y:W[x][y]*W[y][j]) for j in range(2)] for x in range(2)]
        c=[avg(lambda y:K[x][y]**2) for x in range(2)]
        rr=[avg(lambda y:(K[x][y]-p**2)**2) for x in range(2)]
        Lz=[avg(lambda y:(W[x][y]-p)*z[y]) for x in range(2)]
        s=avg(lambda x:z[x]**2); Delta=avg(lambda x:c[x])-p**4
        check(all(c[x]-p**4==2*p**3*z[x]+2*p*p*Lz[x]+rr[x] for x in range(2)),"root square identity")
        check(avg(lambda x:rr[x])==Delta-2*p*p*s,"mean remainder")
        B=avg(lambda x:d[x]*(c[x]-p**4))
        check(B>=4*p**3*s+2*p**2*avg(lambda x:z[x]*Lz[x]),"weighted positivity")
        for a,b in ((3,2),(4,3)):
            for x in range(2):
                h=0
                for ys in product(range(2),repeat=b):
                    val=1
                    for y in ys:val*=pi[y]*W[x][y]
                    def F(i):
                        xprod=1
                        for y in ys:xprod*=W[i][y]
                        return xprod
                    h+=val*avg(F)**(a-1)
                check(h**2>=c[x]**(b*(a-1)),"rooted biclique must dominate square power")
        count+=1
print("Exact finite controls:",count,"two-atom weighted kernels.")
