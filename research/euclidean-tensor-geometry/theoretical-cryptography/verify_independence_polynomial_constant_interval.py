#!/usr/bin/env python3
"""Exact controls for the stronger fixed-rank independence-polynomial constants."""
from itertools import combinations, product
from math import comb


def choose(n,k):
    return comb(n,k) if 0<=k<=n else 0


def upper_distribution(s,k):
    # (1+x)(1+3x+x^2) P'=[s(1+3x+x^2)+k(1+x)(3+2x)] P.
    degree=s+2*k
    p=[0,0,1]
    for j in range(degree+2):
        nxt=((s+3*k-4*j)*p[-1]+(3*s+5*k-4*(j-1))*p[-2]
             +(s+2*k-(j-2))*p[-3])
        v,rem=divmod(nxt,j+1)
        assert not rem
        p.append(v)
    assert p[-2:]==[0,0]
    return p[2:-2]


def coefficients(r,k,t):
    s=r-t
    p=upper_distribution(s,k)
    assert sum(p)==2**s*5**k
    v=[choose(r,i)+(p[i] if i<len(p) else 0)
       for i in range(r+1)]
    for i in range(r+1):
        v[i]-=choose(s+2*k,i)
    v[1]+=1
    return v


def motif_check(r,k,t):
    assert 2*k<=t<=r
    n=r+k+1
    s=r-t
    anchors=[(s+2*i,s+2*i+1) for i in range(k)]
    adj=[0]*n
    def edge(i,j):
        adj[i]|=1<<j
        adj[j]|=1<<i
    for i,j in combinations(range(r),2):
        edge(i,j)
    for i,j in combinations(range(r,r+k),2):
        edge(i,j)
    for u in range(r,r+k):
        for i in range(s+2*k):
            if i not in anchors[u-r]:
                edge(i,u)
    f=[0]*(r+1)
    def recurse(v,k0):
        f[k0]+=1
        while v:
            b=v&-v
            v^=b
            recurse(v&adj[b.bit_length()-1],k0+1)
    recurse((1<<n)-1,0)
    assert f==coefficients(r,k,t)
    assert adj[-1]==0  # universal vertex in the original graph
    return sum(f)


def exact_examples():
    examples=[(1024,230,534,(478,497,509)),(4096,450,1045,(1984,2011,2041))]
    for r,k,t,(a,b,c) in examples:
        v=coefficients(r,k,t)
        assert r==len(v)-1 and v[r]==1
        assert v[a-1]<v[a]>v[a+1]
        assert v[b-1]>v[b]<v[b+1]
        assert v[c-1]<v[c]>v[c+1]
        assert v[b]<min(v[a],v[c])
        print(r,r+k+1,(a,b,c))


def deletion_controls():
    # Independently check every prefix conditional inequality in small instances.
    checks=0
    pairs=list(combinations(range(3),2))
    for links in range(1<<len(pairs)):
        cliques=[m for m in range(8)
                 if all(not (m>>a&1 and m>>b&1) or links>>j&1
                        for j,(a,b) in enumerate(pairs))]
        for neighborhoods in product(range(8),repeat=3):
            weights={}
            for m in cliques:
                w=7
                for i in range(3):
                    if m>>i&1:
                        w&=neighborhoods[i]
                weights[m]=2**w.bit_count()
            for i in range(3):
                for pref in range(1<<i):
                    yes=no=0
                    for m,w in weights.items():
                        if m&((1<<i)-1)!=pref:
                            continue
                        if m>>i&1:
                            assert weights[m^(1<<i)]>=w
                            yes+=w
                        else:
                            no+=w
                    assert yes<=no
                    checks+=1
    return checks


def main():
    # Small motif and overlap enumeration, independent of the recurrence.
    assert motif_check(8,2,5)==329
    assert motif_check(9,3,7)==757
    c=deletion_controls()
    assert c==28672
    exact_examples()
    print("PASS",c,"prefix controls and both strict finite valleys")


if __name__=='__main__':
    main()
