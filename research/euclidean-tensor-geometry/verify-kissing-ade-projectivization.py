#!/usr/bin/env python3
"""Exact exceptional ADE obstruction census. Python 3.10+, standard library.
No solver, rounding, or precomputed root orbit/case list is used.
Coordinates for roots are simple-root coefficients. Coordinates for points
are scalar products with simple roots; vectors from these spaces are distinct.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
from math import lcm
from collections import Counter
if not __debug__:
    raise RuntimeError('Run without -O')
def dot(x,y):
    return sum(a*b for a,b in zip(x,y))
def solve(A,b):
    t=[list(map(F,r)) + [F(s)] for r,s in zip(A,b)]
    n=len(t)
    for i in range(n):
        h=next((j for j in range(i,n) if t[j][i]),None)
        if h is None:return None
        t[i],t[h]=t[h],t[i]
        a=t[i][i];t[i]=[u/a for u in t[i]]
        for j in range(n):
            if j!=i and t[j][i]:
                a=t[j][i];t[j]=[x-a*y for x,y in zip(t[j],t[i])]
    return tuple(r[-1]for r in t)
def le(a,b):return all(x<=y for x,y in zip(a,b))
def reflect(y,i,G):return tuple(t-y[i]*u for t,u in zip(y,G[i]))
def census(n):
    G=[[2*int(i==j)for j in range(n)]for i in range(n)]
    for i,j in [(i,i+1) for i in range(n-2)]+[(2,n-1)]:
        G[i][j]=G[j][i]=-1
    e=[tuple(int(i==j)for j in range(n))for i in range(n)]
    roots=set(e);st=list(e)
    def reflroot(a,i):
        z=list(a);z[i]-=dot(G[i],a);return tuple(z)
    for a in st:
        for i in range(n):
            v=reflroot(a,i)
            if v not in roots:st.append(v);roots.add(v)
    R=sorted(roots);assert len(R)=={6:72,7:126,8:240}[n]
    idx={a:i for i,a in enumerate(R)}
    P=[a for a in R if min(a)>=0]
    gi=tuple(solve(G,a)for a in e)
    gd=lcm(*(x.denominator for row in gi for x in row))
    J=tuple(tuple(int(x*gd) for x in row) for row in gi)
    def norm(y):return dot(y,tuple(dot(j,y)for j in J))/F(gd)
    rootpoints={tuple(dot(g,a)for g in G)for a in R}
    top={a:{b for b in P if a!=b and le(a,b)}for a in P}
    def vertices(C):
        vs={tuple(F(0) for i in e)}
        assert all(any(a[i]>0 for a in C) for i in range(n))
        for k in range(1,min(n,len(C))+1):
            for cols in combinations(range(n),k):
                for rows in combinations(C,k):
                    z=solve([[r[j]for j in cols]for r in rows],[1]*k)
                    if z is None or min(z)<0:continue
                    y=[F(0)]*n
                    for j,v in zip(cols,z):y[j]=v
                    y=tuple(y)
                    if all(dot(y,a)<=1 for a in C):vs.add(y)
        return vs
    todo=[frozenset()];seen=set(todo);clean=[];front=[];gens=set()
    for I in todo:
        C=[a for a in P if a not in I and top[a]<=I]
        if not C or not all(any(a[i]>0 for a in C)for i in range(n)):
            front.append(I);continue
        V=vertices(C)
        if any(norm(y)>2 or (norm(y)==2 and y not in rootpoints) for y in V):
            front.append(I);continue
        clean.append(I);gens.update(V)
        for a in C:
            K=I|{a}
            if K not in seen:todo.append(K);seen.add(K)
    L=lcm(*(t.denominator for y in gens for t in y))
    U=sorted(tuple(int(x*L)for x in y)for y in gens)
    D=L*L*gd
    dual=[tuple(dot(j,y) for j in J)for y in U]
    lens=[dot(y,z)for y,z in zip(U,dual)]
    cand={tuple(sorted(idx[r]for r in I))for I in front}
    interior=set();pairs=0
    for v,V,hv in zip(U,dual,lens):
        if 2*hv<=3*D or hv>=2*D:continue
        neg=[r for r in R if dot(r,v)<-L]
        B={i for i,r in enumerate(R)if dot(r,v)>L}
        for w,hw in zip(U,lens):
            if hw>=2*D:continue
            hh=(2*D-hv)*(2*D-hw)
            def bad(y):
                d=dot(V,y)
                return d< -D and (d+D)**2>hh
            y=w
            while max(y)>0:y=reflect(y,y.index(max(y)),G)
            if not bad(y):continue
            seq=[y];seen={y}
            for y in seq:
                if not any(dot(a,y)>L for a in neg):
                    m=tuple(sorted(B|{i for i,r in enumerate(R) if dot(r,y)>L}))
                    interior.add(m)
                for i,t in enumerate(y):
                    if t:
                        z=reflect(y,i,G)
                        if z not in seen and bad(z):seen.add(z);seq.append(z)
            pairs+=len(seq)
    exterior=set(cand)
    cand|=interior
    # Canonical form: fold the root-set sum, then take its complete
    # orbit under the stabilizer of that dominant sum.
    perm=[[idx[reflroot(r,i)] for r in R] for i in range(n)]
    diag=[4,3,2,1,0,5] if n==6 else list(range(n))
    dp=[idx[tuple(r[j] for j in diag)] for r in R]
    @lru_cache(None)
    def one(M):
        a=tuple(sum(R[t][i] for t in M)for i in range(n))
        y=tuple(dot(g,a)for g in G)
        while min(y)<0:
            i=y.index(min(y))
            M=tuple(sorted(perm[i][t]for t in M));y=reflect(y,i,G)
        S=[i for i,t in enumerate(y)if t==0]
        todo=[M];seen={M}
        for m in todo:
            for i in S:
                z=tuple(sorted(perm[i][t]for t in m))
                if z not in seen:todo.append(z);seen.add(z)
        return min(seen)
    @lru_cache(None)
    def canon(M):
        return min(one(M),one(tuple(sorted(dp[t]for t in M))))
    def signature(M):
        a=tuple(sum(R[t][i]for t in M)for i in range(n))
        y=tuple(dot(g,a)for g in G)
        return tuple(sorted(dot(R[t],y)for t in M))
    mini={};sig={}
    for M in sorted(cand,key=lambda x:(len(x),x)):
        if any(signature(z) in sig[k] and canon(z) in mini[k]
               for k in mini if k<=len(M) for z in combinations(M,k)):continue
        k=len(M);mini.setdefault(k,set()).add(canon(M))
        sig.setdefault(k,set()).add(signature(M))
    def ideal(t):
        a=tuple(map(int,t));assert a in P
        return tuple(sorted(idx[r]for r in P if le(a,r)))
    seeds={6:['012211','112111'],7:['1232112','1222211'],
           8:['13543213','23432212']}[n]
    listed=[ideal(t) for t in seeds]
    if n==6:
        def coord(t):
            sign=-1 if t[0]=='-' else 1
            return tuple(sign*int(x)for x in t.lstrip('-'))
        listed.append(tuple(sorted(idx[coord(t)]for t in
            '-122111 -112111 -111111 -111110 112211 122211 123211 123212'.split())))
    assert {(k,c)for k,v in mini.items()for c in v}=={(len(m),canon(m)) for m in listed}
    # Check the escape classification on its own, not just the combined antichain.
    extcanon={len(m):canon(m)for m in listed[:2]}
    assert all(any(canon(z)==c for k,c in extcanon.items() if k<=len(m)
                   for z in combinations(m,k)) for m in exterior)
    assert all(any(len(m)==k and canon(m)==c for m in exterior)
               for k,c in extcanon.items())
    if n==6:
        vv=(1,0,0,1,0,0);ww=(-2,0,0,1,-2,0) # simple products times 2
        assert tuple(i for i,r in enumerate(R) if max(dot(r,vv),dot(r,ww))>2)==listed[-1]
        assert norm(vv)==norm(ww)==F(22,3)
        assert F(dot(vv,tuple(dot(j,ww)for j in J)),4*gd)==F(-4,3)
    def orbit_size(M):
        qq=[M];ss={M}
        for m in qq:
            for p in perm+([dp] if n==6 else []):
                z=tuple(sorted(p[t]for t in m))
                if z not in ss:qq.append(z);ss.add(z)
        return len(ss)
    counts=tuple(orbit_size(M)for M in listed)
    assert counts=={6:(432,6480,2160),7:(4032,30240),
                    8:(17280,181440)}[n],counts
    count=(len(todo),len(clean),len(front),len(gens),pairs,len(interior))
    assert count=={6:(12,7,5,12,210,4),7:(13,9,4,15,4151,0),
                   8:(19,13,6,20,24106,0)}[n],count
    base=vertices([max(P,key=sum)])
    radius=max(norm(y)for y in base)
    assert radius=={6:F(4,3),7:F(3,2),8:F(1)}[n]
    print('E'+str(n),'states/clean/front/gens/bad-pairs/new masks',*count,
          'nonopposite sizes',list(map(len,listed)),'orbit counts',counts,'PASS',flush=True)
for n in (6,7,8):census(n)
