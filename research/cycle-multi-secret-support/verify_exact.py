#!/usr/bin/env python3
"""Check explicit schemes against full distributions, not just decoder formulas."""
from collections import Counter
from itertools import product

def words(n):
    return list(product((0,1),repeat=n))

def conditions(d):
    n=len(d[0])
    active=[len({x[i] for x in d})>1 for i in range(n)]
    same=[len({x[i]^x[(i+1)%n] for x in d})==1 for i in range(n)]
    if all(not active[i] or same[i-1] or same[i] for i in range(n)):
        return 1,same,None
    if any(same) or len({sum(x)%2 for x in d})==1:
        return 2,same,None
    for tail in product((-1,1),repeat=n-1):
        s=(1,)+tail
        if len({sum(a*b for a,b in zip(s,x))%3 for x in d})==1:
            return 3,same,s
    return 4,same,None

def shares(m,x,r,z,pair,s):
    n=len(x)
    if m==1:
        return [x[i] if pair[i] else 0 for i in range(n)]
    if m==2 and any(pair):
        start=pair.index(True)
        v=[None]*n
        for k in range(n):
            i=(start+k)%n
            v[i]=(x[i] if pair[i] else
                  r if pair[i-1] else v[i-1]^x[i])
        return v
    if m==2:
        a=[(x[i]-z[i])%2 for i in range(n)]
        mod=2
    elif m==3:
        a=[s[i]*(x[i]-z[i])%3 for i in range(n)]
        mod=3
    else:
        # Independent component formulas from (2) directly in bits.
        a=[(sum(x[2:])%2,x[0]),(0,x[1]),(x[2],x[0]^x[1])]
        a.extend((v,0) for v in x[3:])
        y=[r&1,r>>1]
        out=[]
        for i,(p,q) in enumerate(a):
            y[0]^=p
            y[1]^=q
            out.append(y[1] if i==0 else y[0] if i==2 else tuple(y))
        assert y==[r&1,r>>1]
        return out
    v=[]
    t=r
    for delta in a:
        t=(t+delta)%mod
        v.append(t)
    assert t==r
    return v

def check(d, force_four=False):
    m,p,s=conditions(d)
    if force_four: m=4
    seen={}
    for x in d:
        labels=[shares(m,x,r,d[0],p,s) for r in range(m)]
        for i,b in enumerate(x):
            hist=Counter((a[i-1],a[i]) for a in labels)
            k=(i,b)
            if k in seen:
                assert hist==seen[k]
            elif (i,1-b) in seen:
                assert hist.keys().isdisjoint(seen[i,1-b].keys())
            seen[k]=hist
    return m

counts=Counter()
pool=words(4)
for mask in range(1,1<<len(pool)):
    d=[w for i,w in enumerate(pool) if (mask>>i)&1]
    counts[conditions(d)[0]]+=1
assert set(counts)=={1,2,3,4}
tests=0
for n in range(4,10):
    pool=words(n)
    d1=[(0,)*n,(1,)*n]
    d2=[w for w in pool if sum(w)%2==0]
    d3=[w for w in pool if sum(w)%3==0]
    d4=pool
    for i,d in enumerate((d1,d2,d3,d4),1):
        assert check(d)==i,(n,i)
        tests+=1
    assert check(d4,force_four=True)==4
    tests+=1
# Explicit path case: no constant global parity, some pair edges, not fully covered.
d=((0,0,0,0),(0,0,0,1),(1,1,0,0))
assert check(d)==2
tests+=1
print("C4 domains in cases 1/2/3/4:",*(counts[i] for i in range(1,5)))
print(f"Explicit schemes: {tests} complete view-distribution checks; C4 through C9 PASS.")
