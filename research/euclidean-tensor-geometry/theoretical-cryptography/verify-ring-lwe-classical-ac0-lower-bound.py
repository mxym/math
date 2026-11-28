#!/usr/bin/env python3
"""Exact toy checks of the projection dual test and independent reference bins."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from random import Random

rng=Random(714)
def mul(a,b,q):
    d=len(a)
    r=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            r[(i+j)%d] += (-1 if i+j>=d else 1)*x*y
    return tuple(x%q for x in r)
def multrows(q,d,rows):
    X=[tuple(int(i==j) for i in range(d)) for j in range(d)]
    return [tuple(mul(a,b,q)[j] for b in X) for a in rows for j in range(d)]
def dot(a,b,q): return sum(x*y for x,y in zip(a,b))%q

proj=goodcases=0
for q,d,k,h in ((3,4,1,2),(3,4,2,2),(5,2,1,1),(9,2,1,1),(15,2,1,1)):
    sec=list(product(range(q),repeat=d))
    for _ in range(100):
        rows=[tuple(rng.randrange(q) for _ in range(d)) for _ in range(k)]
        m=multrows(q,d,rows)
        for I in combinations(range(d),1):
            for n in range(1,h+1):
                for J in combinations(range(len(m)),n):
                    v=[m[i] for i in J]
                    no_relation=not any(
                        all(sum(c_j*v_j[i] for c_j,v_j in zip(c,v))%q==0
                            for i in range(d) if i not in I)
                        for c in product(range(q),repeat=n) if any(c))
                    hist=Counter(tuple(s[i] for i in I)+tuple(dot(a,s,q) for a in v) for s in sec)
                    onto=len(hist)==q**(len(I)+n)
                    assert onto==no_relation
                    if onto:
                        assert set(hist.values())=={q**(d-len(I)-n)}
                        goodcases+=1
                    proj+=1

# Dummy finite scalar reference with four equiprobable bins and three phases.
C=[[F(1,4)+F(1,12)*g*w for w in (1,0,-1,0)] for g in (1,-1,0)]
assert all(sum(row)==1 and min(row)>=0 for row in C)
assert [sum(row[j] for row in C)/3 for j in range(4)]==[F(1,4)]*4
bins=0
for h in (1,2,3):
    for xs in product(range(4),repeat=h):
        p=F(0)
        for u in product(range(3),repeat=h):
            a=F(1,3**h)
            for i in range(h): a*=C[u[i]][xs[i]]
            p+=a
        assert p==F(1,4**h)
        bins+=1

# Uniform averaging over a list counts each distinct valid projection at most once.
lists=0
for q in (3,5,9):
    for L in (1,2,5):
        out=[[rng.randrange(-2,q+2) for _ in range(L)] for _ in range(16)]
        count=sum(sum(x in v for x in range(q)) for v in out)
        assert count<=len(out)*L
        lists+=1

refbins=bins
# Exact finite Fourier correction and arbitrary adaptive parity-tree leaves.
def parity(x,m): return 1 if ((x&m).bit_count()%2==0) else -1
corrections=trees=0
for n in (3,4,5,6):
    N=1<<n
    for _ in range(30):
        w=[rng.randrange(1,10) for x in range(N)]
        p=[F(a,sum(w)) for a in w]
        coeff=[sum(p[x]*parity(x,m) for x in range(N)) for m in range(N)]
        delta=max(abs(c) for c in coeff[1:])
        low=[m for m in range(1,N) if m.bit_count()<=2]
        Lam=delta*len(low)
        R=[(N*p[x]-sum(coeff[m]*parity(x,m) for m in low)+Lam)/(1+Lam)
           for x in range(N)]
        assert min(R)>=0 and sum(R)==N
        assert all(sum(R[x]*parity(x,m) for x in range(N))==0 for m in low)
        assert sum(abs(R[x]/N-p[x]) for x in range(N))/2<=3*Lam/2
        corrections+=1
        masks=[0]+[rng.randrange(N) for node in range(7)]
        def leaf(x):
            a=1
            for _ in range(3): a=2*a+int(parity(x,masks[a])<0)
            return a
        bins={v:[x for x in range(N) if leaf(x)==v] for v in range(8,16)}
        for X in bins.values():
            if not X: continue
            q_mass=F(len(X),N)
            assert abs(sum(p[x] for x in X)-q_mass)<=delta*(1-q_mass)
            trees+=1
print("PASS dual/surjection cases / onto cases / exact finite reference bins / list checks / Fourier corrections / parity leaves:",
      proj,goodcases,refbins,lists,corrections,trees)
