#!/usr/bin/env python3
"""Independent integer audit of the PSL(2,7) multi-orbit continuous certificate.

Generators on eight coordinates, alternate sum-zero bases, rectangular
Bernstein exclusion of single orbits, and independent signed pair covering.
No input files or packages.
"""
from itertools import product, combinations
from functools import lru_cache
from collections import Counter

pts=tuple(range(8))
tr=tuple((i+1)%7 if i<7 else 7 for i in pts)
iv=tuple(0 if i==7 else 7 if i==0 else -pow(i,-1,7)%7 for i in pts)
def mul(u,v): return tuple(u[i] for i in v)
def closure(gens):
    S={pts}; past=[pts]
    while past:
        g=past.pop()
        for h in gens:
            z=mul(h,g)
            if z not in S:S.add(z);past.append(z)
    return S
G=sorted(closure((tr,iv)))
assert len(G)==168
def blocks(g):
    work=set(pts); out=[]
    while work:
        p=min(work); cyc=[p];q=g[p]
        while q!=p:cyc.append(q);q=g[q]
        work.difference_update(cyc);out.append(tuple(cyc))
    return sorted(out,key=lambda o:(len(o),o[0]))
assert Counter(tuple(map(len,blocks(g))) for g in G)=={
    (1,)*8:1,(2,2,2,2):21,(1,1,3,3):56,(4,4):42,(1,7):48}
T=tuple((2*i)%7 if i<7 else 7 for i in pts)
assert iv in G and T in G
for g,n in [(iv,2),(T,3)]:
    H=frozenset(closure((g,)))
    assert len(H)==n
    def inv(u):
        return tuple(u.index(i) for i in pts)
    assert {frozenset(mul(mul(u,h),inv(u)) for h in H) for u in G} == {
        frozenset(closure((h,))) for h in G if len(closure((h,)))==n}
subsets=set(combinations(pts,4)); bal=[]
while subsets:
    seed=min(subsets); orb={tuple(sorted(g[i] for i in seed)) for g in G}
    subsets-=orb;bal.append(orb)
assert [len(s) for s in bal]==[42,14,14]
assert all(tuple(i for i in pts if i not in s) in o for o in bal for s in o)
outer=tuple((3*i)%7 if i<7 else 7 for i in pts)
assert [{tuple(sorted(outer[i] for i in s)) for s in o} for o in bal] == [bal[0],bal[2],bal[1]]
assert len({tuple(sorted((g[0],g[1]))) for g in G})==28

def dot(x,y):return sum(a*b for a,b in zip(x,y))
def mat(x,y):return tuple(dot(a,b) for a in zip(*x) for b in zip(*y))
def mulq(A,x,y):return sum(x[i]*A[3*i+j]*y[j] for i in range(3) for j in range(3))
def outer3(x):return tuple(a*b for a in x for b in x)
def sym(A):return tuple(A[3*i+j]+A[3*j+i] for i in range(3) for j in range(3))
def mix(A,B,a,b):return tuple(a*x+b*y for x,y in zip(A,B))

@lru_cache(None)
def data(order,simp,balidx):
    g=iv if order==2 else T
    H=closure((g,))
    rows=[None]*8
    S=([(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)] if order==2 else
       [(1,-3,0),(-1,-3,0),(0,1,1),(0,1,-1)])
    for o,r in zip(blocks(g),S):
        for i in o:rows[i]=r
    Q=mat(rows,rows)
    assert Q == ((8,0,0,0,8,0,0,0,8) if order==2 else (2,0,0,0,24,0,0,0,6))
    matrices={}
    for h in G:matrices[h]=mat(rows,[rows[h[i]] for i in pts])
    necessary={mix(sym(M),Q,1,-1) for h,M in matrices.items() if h not in H}
    if simp:
        for a in rows:necessary.add(mix(outer3(a),Q,32,-7))
    for j in balidx:
        for s in bal[j]:
            a=tuple(sum((1 if i in s else -1)*rows[i][k] for i in pts) for k in range(3))
            necessary.add(mix(outer3(a),Q,1,-2))
    return tuple(sorted(necessary)),Q,tuple(sorted(set(matrices.values())))

# Box coordinate integer numerators; actual box is [u,U] × [v,V] divided
# by d with the remaining coordinate fixed to ±1.  Binary cuts alternate
# the axes and retain both closed halves.
def roots():
    return [(f,-d,d,-d,d,d,0) for f in (-3,-2,-1,1,2,3) for d in (1,)]
def cuts(box):
    f,u,U,v,V,d,t=box
    if t%2==0:
        return [(f,2*u,u+U,2*v,2*V,2*d,t+1),(f,u+U,2*U,2*v,2*V,2*d,t+1)]
    return [(f,2*u,2*U,2*v,v+V,2*d,t+1),(f,2*u,2*U,v+V,2*V,2*d,t+1)]
def lift(f,d,p,q):
    i=abs(f)-1
    out=[p,q];out.insert(i,d if f>0 else -d);return tuple(out)
@lru_cache(None)
def square_grid(box):
    f,u,U,v,V,d,t=box
    return tuple(tuple(lift(f,2*d,a,b) for b in (2*v,v+V,2*V)) for a in (2*u,u+U,2*U))

@lru_cache(None)
def corners(box):
    f,u,U,v,V,d,_=box
    return tuple(lift(f,d,a,b) for a,b in product((u,U),(v,V)))
def eroot_cone(box):
    vs=corners(box)
    return any(all(sign*p>4*abs(t) and 2*sign*p>abs(s) for p,t,s in vs)
               for sign in (1,-1))

def positive_quadratic(C,box):
    # Quadratic of two variables. Interpolation at 0,1/2,1, followed
    # by degree-2 Bernstein conversion with positive common integer scale.
    X=square_grid(box)
    val=[[mulq(C,x,x) for x in row] for row in X]
    if min(val[0][0],val[0][2],val[2][0],val[2][2])<=0:return False
    def interpolate(row):return (2*row[0],4*row[1]-row[0]-row[2],2*row[2])
    return min(k for c in zip(*(interpolate(r) for r in val)) for k in interpolate(c))>0

@lru_cache(None)
def feasible(order,simp,which,cone,box):
    if cone and eroot_cone(box):return False
    return not any(positive_quadratic(C,box) for C in data(order,simp,which)[0])

def scan(order,simp,which,cone=False,stop=20):
    stack=roots();remain=[];n=0
    while stack:
        B=stack.pop();n+=1
        if not feasible(order,simp,which,cone,B):continue
        if B[-1]==stop:remain.append(B)
        else:stack.extend(cuts(B))
    return remain,n

def pair():
    kept,n=scan(3,True,(),stop=6);Q,matrices=data(3,True,())[1:]
    stack=[(B,C) for B in kept if B[0]>0 for C in kept]
    steps=0
    @lru_cache(None)
    def upper(B):
        return max(mulq(Q,b,b) for b in corners(B))
    while stack:
        B,C=stack.pop();steps+=1
        if not feasible(3,True,(),False,B) or not feasible(3,True,(),False,C):continue
        lim=upper(B)*upper(C)
        U,V=corners(B),corners(C)
        exclude=False
        for M in matrices:
            m=mulq(M,U[0],V[0])
            if m<=0 or 4*m*m<=lim:continue
            v=min(mulq(M,x,y) for x in U for y in V)
            if v>0 and 4*v*v>lim:
                exclude=True;break
        if exclude:continue
        assert max(B[-1],C[-1])<26,(B,C)
        if B[-1]<=C[-1]:stack.extend((Z,C) for Z in cuts(B))
        else:stack.extend((B,Z) for Z in cuts(C))
    return n,len(kept),steps

if __name__=="__main__":
    for args in [(2,True,()),(3,True,(0,)),(3,True,(1,)),(3,True,(2,)),
                 (2,False,(0,)),(3,False,(0,1,2),True)]:
        remain,n=scan(*args)
        assert not remain,(args,len(remain),remain[:2])
        print(args,n,flush=True)
    print("pair",pair(),flush=True)
