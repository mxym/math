#!/usr/bin/env python3
"""Exact small-field checks for order-12 polarity reductions."""
from collections import Counter
from itertools import combinations, product


def require(ok,msg):
    if not ok:
        raise AssertionError(msg)


def model(q,poly):
    def mul(a,b):
        out=0
        while b:
            if b&1:
                out^=a
            b>>=1
            a<<=1
            if a&q:
                a^=poly
        return out
    inv={a:next(b for b in range(1,q) if mul(a,b)==1) for a in range(1,q)}
    def norm(x):
        a=next(h for h in x if h)
        return tuple(mul(h,inv[a]) for h in x)
    P=sorted({norm(x) for x in product(range(q),repeat=3) if any(x)})
    idx={x:i for i,x in enumerate(P)}
    def dot(a,b):
        return mul(a[0],b[0]) ^ mul(a[1],b[1]) ^ mul(a[2],b[2])
    adj=[{j for j,v in enumerate(P) if not dot(u,v)} for u in P]
    return P,idx,norm,adj


def check(q, poly):
    P,idx,norm,adj=model(q,poly)
    A={i for i,row in enumerate(adj) if i in row}
    pole=adj.index(A)
    require(len(A)==q+1 and pole not in A,"wrong pole")
    X=set(range(len(P)))-{pole}-A
    groups={i:adj[i]&X for i in A}
    require(len(P)==q*q+q+1 and set().union(*groups.values())==X,"bad fiber union")
    f={i:a for a,row in groups.items() for i in row}
    require(len(f)==sum(map(len,groups.values())),"fibers overlap")

    # Check directly that two ambient points have just one common neighbor.
    require(all(len(adj[i]&adj[j])==1 for i,j in combinations(range(len(P)),2)),
            "incorrect projective incidence")
    triangles={tuple(sorted((i,j,k))) for i in X for j in adj[i]&X
               for k in adj[i]&adj[j] if k!=i and k!=j}
    require(all(set(T)<=X for T in triangles),"triangle has an absolute or pole")
    subplanes={}
    point_hits=Counter()
    abs_pairs=Counter()
    mixed=Counter()
    for T in triangles:
        B=frozenset({pole,*T,*(f[i] for i in T)})
        require(len(B)==7 and all(len(adj[i]&B)==3 for i in B),"not Fano")
        require(all(len(adj[i]&adj[j]&B)==1 for i,j in combinations(B,2)),
                "wrong Fano joins")
        require(B not in subplanes,"two triangle generators")
        subplanes[B]=T
        point_hits.update(B)
        abs_pairs.update(combinations(sorted(B&A),2))
        mixed.update((a,i) for a in B&A for i in B&X)
    ex=q*(q*q-1)//6
    require(len(subplanes)==ex and point_hits[pole]==ex,"Fano total")
    require(all(point_hits[a]==q*(q-1)//2 for a in A),"absolute vertex profile")
    require(all(point_hits[i]==q//2 for i in X),"nonabsolute vertex profile")
    require(all(abs_pairs[p]==q-1 for p in combinations(sorted(A),2)),"absolute pair profile")
    require(all(mixed[a,i]==(q//2 if a==f[i] else 1) for a in A for i in X),"mixed pair profile")
    if q<=4:
        direct=set()
        for B in combinations(range(len(P)),7):
            S=frozenset(B)
            if all(len(adj[i]&S)==3 for i in S) and all(len(adj[i]&adj[j]&S)==1
                                                       for i,j in combinations(S,2)):
                direct.add(S)
        require(direct==set(subplanes),"independent seven-point census")

    # Two very different collineations commuting with transpose polarity.
    t2=tuple(idx[norm((y,x,z))] for x,y,z in P)
    t3=tuple(idx[norm((z,x,y))] for x,y,z in P)
    for T in (t2,t3):
        require(all({T[j] for j in row}==adj[T[i]] for i,row in enumerate(adj)),"not a collineation")
    fixed2=sum({t2[i] for i in B}==B for B in subplanes)
    fixed3=sum({t3[i] for i in B}==B for B in subplanes)
    require(fixed2==q//2,"involution count")
    tr3=sum(t3[i] in adj[i] for i in range(len(P)))
    if q in (2,8):
        require(tr3==q+1 and fixed3==tr3//3,"odd-order trace data")
    print(q,ex,fixed2,fixed3,tr3)


def fano_correlations():
    P,idx,norm,adj=model(2,3)
    atlas=Counter()
    for A in product((0,1),repeat=9):
        def image(x, trans=False):
            return tuple(sum(x[j]*A[((3*j+i) if trans else (3*i+j))] for j in range(3))%2
                         for i in range(3))
        F=[image(x) for x in P]
        if len(set(F))!=7 or not all(any(v) for v in F):
            continue
        l=[idx[a] for a in F]
        reinv={image(y,True):i for i,y in enumerate(P)}
        L=[reinv[x] for x in P]
        T=[L[l[i]] for i in range(7)]
        require(all((p in adj[a])==(L[a] in adj[l[p]]) for p in range(7) for a in range(7)),
                "wrong incidence-reversing action")
        w=list(range(7));s=0
        while True:
            w=[T[i] for i in w];s+=1
            if w==list(range(7)):
                break
        atlas[2*s]+=1
    require(sum(atlas.values())==168 and not atlas[4],"unexpected Fano correlation atlas")
    print("Fano correlation orders",sorted(atlas.items()))


if __name__=="__main__":
    for q,p in [(2,0b11),(4,0b111),(8,0b1011)]:
        check(q,p)
    fano_correlations()
    print("PASS")
