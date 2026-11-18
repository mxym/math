"""Exact tests of the single-hub coefficient inequality, including a stronger pinned form.
Counts directly in the original independent-set model without boundary sorting.
All vertices are indexed within their own bipartition; left 0 is the hub.
"""
from itertools import product, permutations
from functools import lru_cache
from math import comb,prod
from random import Random
rng=Random(20111017)
def check(ok,msg):
    if not ok:raise ArithmeticError(msg)
@lru_cache(None)
def choices(m,p):
    return tuple(x for x in range(1<<m) if x.bit_count()==p)
@lru_cache(None)
def image(x,pi):
    return sum((x>>i&1)<<v for i,v in enumerate(pi))
def binom(n,r):
    return comb(n,r) if 0<=r<=n else 0
def counts(neigh,la,ra,m,perms):
    # neigh[j] is the set of left neighbors of the jth right node
    out={}
    for L in product(*(choices(m,a) for a in la)):
        subtotal=1
        for N,a,s in zip(neigh,ra,perms):
            bad=0
            for v in N:bad|=(L[v] if v else image(L[v],s))
            subtotal*=binom(m-bad.bit_count(),a)
        out[L[0]]=out.get(L[0],0)+subtotal
    return out
def extendable(neigh,pin,pi,m,nl):
    # Transport a single hub subset breadth-first on the actual gained graph,
    # testing whether all traversals are consistent. No orbit/count formula.
    lab={0:pin};stack=[0];IR=tuple(range(m))
    edges=[[] for _ in range(nl+len(neigh))]
    for j,N in enumerate(neigh):
        for i in N:
            pp=pi[j] if i==0 else IR
            ip=tuple(pp.index(k) for k in IR)
            edges[i].append((nl+j,pp));edges[nl+j].append((i,ip))
    while stack:
        u=stack.pop()
        for v,s in edges[u]:
            b=image(lab[u],s)
            if v in lab:
                if lab[v]!=b:return False
            else:lab[v]=b;stack.append(v)
    return True
totals=[0,0,0,0,0]
def test(neigh,m,la,ra,pi):
    I=tuple(range(m));rid=tuple(range(m-2));nl=len(la)
    Z=counts(neigh,la,ra,m,pi); P=counts(neigh,la,ra,m,[I]*len(ra))
    reduced=counts(neigh,[a-1 for a in la],[a-1 for a in ra],m-2,[rid]*len(ra))
    reserve=sum(reduced.values());den=comb(m-2,la[0]-1)
    check(reserve%den==0 and reserve>0, ('reserve',m,la,ra))
    unstable=0
    for A,z in Z.items():
        flat=extendable(neigh,A,pi,m,nl)
        check(P[A]-z>=(not flat)*(reserve//den), ('pinned',m,la,ra,pi,A))
        if flat:check(P[A]==z, ('equality',m,la,ra,pi,A))
        unstable+=not flat;totals[1]+=1
    D=sum(P.values())-sum(Z.values())
    check(D*den>=unstable*reserve, ('total',m,la,ra,pi))
    if len(set(list(la)+[m-v for v in ra]))==1:
        check(D*den==unstable*reserve, ('saturated',m,la,ra,pi))
        totals[2]+=1
    if unstable:
        check(unstable>=2*den and D>=2*reserve, ('uniform',m,la,ra,pi))
        totals[3]+=1
    else:check(D==0, ('flat',m,la,ra,pi))
    if den>1:totals[4]+=1
    totals[0]+=1

I=tuple(range(3));S=tuple(permutations(I))
# Cube Q3 is the 4-crown, triconnected, not chordal bipartite, treewidth≥3.
crown4=[tuple(v for v in range(4) if v!=j) for j in range(4)]
for la in product((1,2),repeat=4):
    for ra in product((1,2),repeat=4):
        if any(la[i]+ra[j]>3 for j,N in enumerate(crown4) for i in N):continue
        for p,q in product(S,repeat=2):
            test(crown4,3,la,ra,(I,I,p,q))
# Two squares meeting only at hub: neighbor requirements from different
# components can differ harmlessly; include both flat and conflicting cases.
bow=[(0,1),(0,1),(0,2),(0,2)]
for i in range(260):
    m=rng.choice((2,3,4,5));s=list(permutations(range(m)));d=rng.randrange(1,m)
    la=[rng.randrange(1,m) for _ in range(3)]
    ra=[rng.randint(1,m-max(la[u] for u in N)) for N in bow]
    pp=[rng.choice(s) for _ in bow]
    if i%4==0:pp=[pp[0],pp[0],pp[2],pp[2]]
    if i%7==0:la,ra=[d]*3,[m-d]*4
    test(bow,m,la,ra,pp)
# Five-crown: known seam classes cannot include this graph.
crown5=[tuple(v for v in range(5) if v!=j) for j in range(5)]
S4=list(permutations(range(4)))
for k in range(12):
    p=rng.choice((1,2,3))
    la=[p]*5 if k%2==0 else [rng.randrange(1,4) for _ in range(5)]
    ra=[4-p]*5 if k%2==0 else [rng.randint(1,4-max(la[i] for i in N)) for N in crown5]
    test(crown5,4,la,ra,[rng.choice(S4) for _ in range(5)])
print('profile-cover instances, pinned subsets, saturated equality cases, nonflat instances, nontrivial reserve denominators:',*totals)
print('PASS: direct independent-set counts, conditional deficits, invariant subset sharpness, disconnected hub complement, crowns.')

# Allow zero/full occupations. Check the equality criterion by detecting
# inconsistent single-label transports after deleting inactive vertices.
def active_flat(neigh,la,ra,m,pi):
    nl=len(la);edges=[[] for _ in range(nl+len(ra))];I=tuple(range(m))
    for j,N in enumerate(neigh):
        for i in N:
            if not la[i] or not ra[j]:continue
            pp=pi[j] if i==0 else I
            edges[i].append((nl+j,pp));edges[nl+j].append((i,tuple(pp.index(k) for k in I)))
    aligned={}
    for v in range(len(edges)):
        if v in aligned:continue
        aligned[v]=I;stack=[v]
        while stack:
            u=stack.pop()
            for w,t in edges[u]:
                pp=tuple(t[j] for j in aligned[u])
                if w in aligned:
                    if aligned[w]!=pp:return False
                else:aligned[w]=pp;stack.append(w)
    return True
boundarytests=[0,0,0]
for k in range(350):
    m=rng.choice((1,2,3,4));I=tuple(range(m));S=tuple(permutations(I))
    la=[rng.randint(0,m) for _ in range(4)]
    ra=[rng.randrange(m+1) if k%3==0 else rng.randint(0,m-max(la[u] for u in N)) for N in crown4]
    pi=[rng.choice(S) for _ in crown4]
    feasible=all(la[v]+ra[j]<=m for j,N in enumerate(crown4) for v in N)
    z=sum(counts(crown4,la,ra,m,pi).values());q=sum(counts(crown4,la,ra,m,[I]*4).values())
    if feasible:
        af=active_flat(crown4,la,ra,m,pi)
        check((q==z)==af and z<=q and q>0,'active graph')
        boundarytests[bool(af)]+=1
    else:
        check(q==z==0,'infeasible');boundarytests[2]+=1
print('Boundary trials (feasible nonflat, feasible flat, infeasible):',*boundarytests)
