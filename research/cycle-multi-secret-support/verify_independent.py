#!/usr/bin/env python3
"""Exhaust local laws and noncommutative loop products; no encoder imports."""
from collections import Counter,defaultdict
from itertools import permutations,product

def pairs(weights):
    # Any marginal has at most three atoms. All relabelings are allowed.
    T=tuple(product(range(3),repeat=3))
    d=defaultdict(set)
    for a,b in product(T,repeat=2):
        A=[0,0,0]; B=[0,0,0]; V=[0]*9
        for i,w in enumerate(weights):
            A[a[i]]+=w;B[b[i]]+=w;V[3*a[i]+b[i]]+=w
        d[tuple(A),tuple(B)].add(tuple(V))
    nb=0
    for (A,B),vals in d.items():
        vals=list(vals)
        for i,V in enumerate(vals):
            for W in vals[i+1:]:
                if any(a and b for a,b in zip(V,W)): continue
                nb+=1
                if weights==(1,1,1):
                    assert A==B==(1,1,1)
                else:
                    fine=(1,1,2)
                    candidates=(tuple(sorted(x for x in A if x)),
                                tuple(sorted(x for x in B if x)))
                    assert all(c in ((2,2),fine) for c in candidates)
                    assert candidates!=(fine,fine)
                    def xor(T):
                        def bit(x,i):
                            if tuple(sorted(y for y in x if y))==fine:
                                return int(x[i]!=2)
                            return int(i!=next(j for j in range(3) if x[j]))
                        e={bit(A,j//3)^bit(B,j%3)
                           for j,v in enumerate(T) if v}
                        assert len(e)==1
                        return e.pop()
                    assert xor(V)!=xor(W)
    return nb

def permloops(n):
    G=list(permutations(range(3)))
    mult=[[G.index(tuple(g[h[i]] for i in range(3))) for h in G] for g in G]
    Id=G.index((0,1,2))
    inv=[next(j for j in range(6) if mult[i][j]==Id) for i in range(6)]
    F=[j for j,p in enumerate(G) if all(p[i]!=i for i in range(3))]
    X=list(product((0,1),repeat=n))
    # Base word is 0. Reversals of bit labels cover any other base word.
    found=set()
    checks=0
    for g0 in product(range(6),repeat=n-1):
        prod=Id
        for v in g0: prod=mult[v][prod]
        g=g0+(inv[prod],)
        for f in product(F,repeat=n):
            h=[(g[i],mult[f[i]][g[i]]) for i in range(n)]
            mask=0
            for j,x in enumerate(X):
                A=Id
                for i,b in enumerate(x): A=mult[h[i][b]][A]
                if A==Id: mask|=1<<j
            found.add(mask)
            checks+=1
    desired=set()
    for s in product((-1,1),repeat=n):
        desired.add(sum(1<<j for j,x in enumerate(X)
                        if sum(a*b for a,b in zip(x,s))%3==0))
    assert found==desired
    return checks,len(found)

def domain_counts():
    # C4 bitset implementation independently builds each property as
    # containment in a fiber of a Boolean or ternary function.
    n=4
    def fibers(f,r):
        a=[0]*r
        for x in range(1<<n): a[f(x)]|=1<<x
        return a
    def fixed(D,ys):
        return any(D&~y==0 for y in ys)
    X=[fibers(lambda x:(x>>i)&1,2) for i in range(n)]
    E=[fibers(lambda x:((x>>i)^(x>>((i+1)%n)))&1,2) for i in range(n)]
    P=fibers(lambda x:x.bit_count()%2,2)
    T=[]
    for s in product((-1,1),repeat=n):
        T.extend(fibers(lambda x:sum(s[i]*((x>>i)&1) for i in range(n))%3,3))
    C=[0]*4
    for D in range(1,1<<(1<<n)):
        e=[fixed(D,z) for z in E]
        if all(e[i] or e[i-1] or fixed(D,X[i]) for i in range(n)):
            C[0]+=1
        elif any(e) or fixed(D,P):
            C[1]+=1
        elif fixed(D,T):
            C[2]+=1
        else:
            C[3]+=1
    return C

u,q=pairs((1,1,1)),pairs((2,1,1))
assert u and q
loop,nm=permloops(4)
counts=domain_counts()
print(f"Independent local disjoint-view pairs: U={u}, Q={q}, all necessary types PASS.")
print(f"Independent S3 enumeration: {loop} noncommutative loop tables, {nm} signed fibers.")
print("Independent bitset C4 counts:",*counts)
