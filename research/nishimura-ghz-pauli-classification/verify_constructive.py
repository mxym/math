#!/usr/bin/env python3
"""Generate each protocol from its graph and test all inputs and seeds exactly."""
from collections import Counter
from itertools import combinations
from random import Random

def bit(x,i):
    return (x>>i)&1

def parity(x):
    return x.bit_count()&1

def quad(x,edges):
    return sum(bit(x,i)*bit(x,j) for i,j in edges)&1

def construct(k,edges,linear,const):
    assert k>=3 and k%2
    X=range(1<<k)
    nbor=[0]*k
    for i,j in edges:
        nbor[i]+=1
        nbor[j]+=1
    active=sum(1<<i for i,d in enumerate(nbor) if d)
    mask=(1<<k)-1
    iso=(active!=mask)
    if not (iso or all(d%2==0 for d in nbor)):
        return None
    def qmap(x):
        a=x&active
        return (a>>1)^(((1<<(k-1))-1) if a&1 else 0)
    # The linear adjustment cancels the derivative along all ones
    # when the quotient loses that direction.
    K=int(not iso and len(edges)%2)
    G={}
    for x in X:
        s=qmap(x)
        val=quad(x,edges)^(K&x)
        assert G.setdefault(s,val)==val
    W=sorted(G)
    rank=active.bit_count() if iso else k-1
    assert len(W)==1<<rank
    output=Counter()
    nq=0
    for t in W:
        wa=[const^parity((linear^K)&x)^G[qmap(x)]^G[qmap(x)^t] for x in X]
        coeff=sum((wa[1<<i]^wa[0])<<i for i in range(k))
        for x in X:
            assert wa[x]==wa[0]^parity(coeff&x)
            # Each player now calculates its own p_i, z_i.
            p=sum((bit(active,i)*bit(x,i)^
                   (bit(t,i-1) if i else 0))<<i for i in range(k))
            z=sum((bit(coeff,i)*bit(x,i)^(wa[0] if not i else 0))<<i
                  for i in range(k))
            q=(p>>1)^(((1<<(k-1))-1) if p&1 else 0)
            w=parity(z)
            y=quad(x,edges)^parity(linear&x)^const
            assert q==t^qmap(x) and y==w^G[q]
            output[x,q,w]+=1
            nq+=1
    expected=[frozenset((q,G[q]^f,1) for q in W) for f in (0,1)]
    for x in X:
        f=quad(x,edges)^parity(linear&x)^const
        assert frozenset((q,w,output[x,q,w]) for q in W for w in (0,1)
                         if output[x,q,w])==expected[f]
    assert expected[0].isdisjoint(expected[1])
    return rank,nq

three_cases=0
hist=Counter()
for g in range(8):
    es=[e for j,e in enumerate(combinations(range(3),2)) if bit(g,j)]
    for a in range(8):
        for b in (0,1):
            ans=construct(3,es,a,b)
            assert (ans is not None)==(g.bit_count()!=2)
            if ans is None: continue
            three_cases+=1
            wt=sum(quad(x,es)^parity(a&x)^b for x in range(8))
            hist[wt]+=1
assert three_cases==80 and sorted(hist.items())==[(0,1),(2,16),(4,46),(6,16),(8,1)]
print("all 80 three-bit Pauli protocols: perfect correctness/privacy PASS")
print("three-bit feasible truth-table weight counts: 0:1 2:16 4:46 6:16 8:1")

rng=Random(1801)
g5ok=g5bad=g5cases=0
es5=list(combinations(range(5),2))
for i in range(1<<len(es5)):
    chosen=[e for j,e in enumerate(es5) if bit(i,j)]
    ans=construct(5,chosen,31,rng.randrange(2))  # all input bits essential
    if ans is None:
        g5bad+=1
    else:
        encodings=ans[0]
        assert encodings<=4
        g5ok+=1
        g5cases+=ans[1]
assert g5ok==294 and g5bad==730
print(f"five-bit graphs: {g5ok} constructive, {g5bad} excluded by criterion; {g5cases} actual input/seed pairs PASS")

es7=list(combinations(range(7),2))
native=[(i,i+1) for i in range(6)]+[(0,6)]
g7positive=0
for trial in range(60):
    if trial%3==0:
        # Keep vertex seven isolated.
        es=[e for e in es7 if 6 not in e and rng.randrange(2)]
    elif trial%3==1:
        es=native[:]
    else:
        # An added chord preserves all degrees positive and
        # makes the two ends odd.
        es=native+[(1,4)]
    ans=construct(7,es,127,rng.randrange(2))
    assert (ans is not None)==(trial%3!=2)
    g7positive+=ans is not None
print(f"seven-bit odd-party sanity: {g7positive} constructive, 20 degree-parity controls PASS")
