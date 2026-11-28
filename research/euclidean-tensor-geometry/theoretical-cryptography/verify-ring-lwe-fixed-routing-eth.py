#!/usr/bin/env python3
"""Finite checks of rearrangeable routing and the exact constraint/score gadgets."""
from itertools import permutations, product
from random import Random

class Net:
    def __init__(self,n,c):
        self.n=n
        self.I=[next(c) for _ in range(n)]
        self.O=[next(c) for _ in range(n)]
        if n==1:
            self.edge={tuple(sorted((self.I[0],self.O[0])))}
            return
        self.sub=[Net(n//2,c),Net(n//2,c)]
        self.edge=set().union(*(u.edge for u in self.sub))
        for i in range(n):
            for u in self.sub:
                self.edge.add(tuple(sorted((self.I[i],u.I[i//2]))))
                self.edge.add(tuple(sorted((u.O[i//2],self.O[i]))))
    def route(self,p):
        n=self.n
        if n==1: return [[self.I[0],self.O[0]]]
        neigh=[[] for i in range(n)]
        inv=[[] for i in range(n//2)]
        for i in range(n):
            neigh[i].append(i^1)
            inv[p[i]//2].append(i)
        for i,j in inv:
            neigh[i].append(j)
            neigh[j].append(i)
        color=[-1]*n
        for i in range(n):
            if color[i]>=0: continue
            color[i]=0; todo=[i]
            while todo:
                k=todo.pop()
                for j in neigh[k]:
                    if color[j]<0:
                        color[j]=1-color[k]
                        todo.append(j)
                    assert color[j]!=color[k]
        Q=[]
        for t,u in enumerate(self.sub):
            sub=[None]*(n//2)
            for i in range(n):
                if color[i]==t: sub[i//2]=p[i]//2
            assert sorted(sub)==list(range(n//2))
            Q.append(u.route(sub))
        return [[self.I[i]]+Q[color[i]][i//2]+[self.O[p[i]]] for i in range(n)]

rng=Random(207)
routes=0
for n in (1,2,4,8,16,32,64):
    R=Net(n,iter(range(1000000)))
    assert len(R.edge)==n*(1+4*(n.bit_length()-1))
    ts=list(permutations(range(n))) if n<=4 else [rng.sample(range(n),n) for i in range(200)]
    for p in ts:
        paths=R.route(p)
        used=set()
        for i,path in enumerate(paths):
            assert path[0]==R.I[i] and path[-1]==R.O[p[i]]
            assert all(tuple(sorted((a,b))) in R.edge for a,b in zip(path,path[1:]))
            assert len(set(path))==len(path) and not used.intersection(path)
            used.update(path)
            routes+=1

# Verify graph routes with data-dependent mapping of a toy constraint host.
host=0
N=4;n=4*N
R=Net(n,iter(range(1000000)))
possible=[(a,b) for a in range(N) for b in range(a+1,N)]
for _ in range(60):
    constraints=[(i,j,rng.randrange(2)) for i,j in possible if rng.randrange(3)]
    idx=[0]*N
    p=[None]*n
    for c,(i,j,neq) in enumerate(constraints):
        p[3*i+idx[i]]=2*c
        p[3*j+idx[j]]=2*c+1
        idx[i]+=1;idx[j]+=1
    rem=iter(sorted(set(range(n))-set(p)))
    for i in range(n):
        if p[i] is None: p[i]=next(rem)
    paths=R.route(p)
    for s in product(range(3),repeat=N):
        out={}
        for i,path in enumerate(paths):
            label=s[i//3] if i<3*N else 0
            for k in path: assert k not in out; out[k]=label
        for j,(a,b,neq) in enumerate(constraints):
            assert ((out[R.O[2*j]]!=out[R.O[2*j+1]])==bool(neq))==((s[a]!=s[b])==bool(neq))
        host+=1

logic=0
def nae(*a): return len(set(a))>1
for t in product((0,1),repeat=4):
    a,b,c,f=t
    assert nae(*t)==any(nae(a,b,w) and nae(1-w,c,f) for w in (0,1))
    logic+=1
for seq in product((0,1),repeat=3):
    assert nae(*seq)==any(all(a!=b for a,b in zip(seq,col)) for col in permutations(range(3)))
    logic+=1

score=0
for q in (3,5,7,11):
    for _ in range(20):
        h=[10]+[0]*(q-1)
        for a in range(1,(q+1)//2): h[a]=h[-a]=rng.randrange(-5,9)
        H=sum(h)
        gain=q*(q*h[0]-H)
        for z in range(q):
            eq=sum(q*(q-1)*h[-u*z%q] for u in range(1,q))
            ne=sum(q*h[(c-u*z)%q] for c in range(1,q) for u in range(1,q))
            eq0=q*(q-1)*(q-1)*h[0]
            ne0=q*(q-1)*(H-h[0])
            assert eq-eq0 == (0 if not z else -(q-1)*gain)
            assert ne-ne0 == (gain if z else 0)
            score+=1

print("PASS disjoint routed paths / host coloring consistency / Boolean gadgets / score factors:",
      routes,host,logic,score)
