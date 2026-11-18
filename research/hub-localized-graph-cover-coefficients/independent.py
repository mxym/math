"""Independent test via a sheet-polynomial product for the graph minus the hub.
No original-space summation over all choices on one bipartition, no BFS test
of extendibility. All counts are integers. Run using Python 3.10+.
"""
from functools import lru_cache
from itertools import product, permutations, combinations
from math import comb,prod
from random import Random
from collections import deque
RNG=Random(221109)
def ck(yes,info):
    if not yes:raise ArithmeticError(info)
@lru_cache(None)
def masks(m,p):return tuple(sum(1<<i for i in b) for b in combinations(range(m),p))
def image(pi,S):return sum(1<<j for i,j in enumerate(pi) if S>>i&1)
def group(components,pi,m):
    # Each component lists the global indices of its boundary demands.
    I=tuple(range(m));gs=[]
    for ix in components:
        for j in ix[1:]:
            gs.append(tuple(pi[ix[0]].index(pi[j][v]) for v in range(m)))
    H={I};todo=deque([I])
    while todo:
        q=todo.popleft()
        for g in gs:
            r=tuple(g[q[i]] for i in range(m))
            if r not in H:H.add(r);todo.append(r)
    F=(1<<m)-1;orbits=[]
    while F:
        i=(F&-F).bit_length()-1;o={g[i] for g in H}
        orbits.append(len(o));F^=sum(1<<x for x in o)
    counts=[1]
    for b in orbits:
        new=counts+[0]*b
        for k,a in enumerate(counts):new[b+k]+=a
        counts=new
    return H,counts,tuple(sorted(orbits))
# A component is (number of vertices, directed inclusions l -> r, boundary vertices).
@lru_cache(None)
def one_sheet(conf,forced):
    n,E,W=conf
    return tuple(tuple((mask>>j)&1 for j in range(n))
                 for mask in range(1<<n)
                 if mask&forced==forced and all((mask>>l&1)<=(mask>>r&1) for l,r in E))
@lru_cache(None)
def F(conf,ranks,m,T):
    n,E,W=conf
    if not all(0<=p<=m for p in ranks):return 0
    # A label contributes one binary column whose support is an up-set
    # containing the forced boundary vertices. Take desired coefficient of
    # the product over labels by dynamic programming.
    demands=sorted(sum(1<<v for v,A in zip(W,T) if A>>j&1) for j in range(m))
    @lru_cache(None)
    def solve(j,r):
        if j==m:return int(not any(r))
        return sum(solve(j+1,tuple(a-b for a,b in zip(r,x)))
                   for x in one_sheet(conf,demands[j])
                   if all(0<=a-b<=m-j-1 for a,b in zip(r,x)))
    return solve(0,ranks)
def shift(A,i,j):
    if A>>j&1 and not A>>i&1:return A^(1<<i)^(1<<j)
    return A
star2=(3,((0,1),(0,2)),(1,2))
star3=(4,((0,1),(0,2),(0,3)),(1,2,3))
p5=(5,((1,0),(1,2),(3,2),(3,4)),(0,2,4))
squaretail=(5,((0,2),(0,3),(1,2),(1,3),(1,4)),(2,3,4))
twig=(1,(),(0,))
counts=[0]*5
def case(comps,m,p,rs,pi):
    I=list(range(m));groups=[];start=0
    for c in comps:
        groups.append(tuple(range(start,start+len(c[2]))));start+=len(c[2])
    H,coef,orbits=group(groups,pi,m)
    A0=(1<<p)-1
    Ppin=prod(F(c,r,m,(A0,)*len(c[2])) for c,r in zip(comps,rs))
    # Compute R (not a priori divided by the denominator) by explicit summation
    # over the reduced pinned sets. This also checks the pinned factorization.
    red=tuple(tuple(x-1 for x in r) for r in rs)
    rv=[prod(F(c,r,m-2,(T,)*len(c[2])) for c,r in zip(comps,red))
        for T in masks(m-2,p-1)]
    den=comb(m-2,p-1);res=sum(rv)
    ck(min(rv)>0 and res==rv[0]*den,'pinned reserve')
    Z=0;fi=0
    for A in masks(m,p):
        stable=all(image(g,A)==A for g in H);fi+=stable
        Ts=tuple(image(g,A) for g in pi);z=1
        for c,r,ix,r0 in zip(comps,rs,groups,red):
            t=tuple(Ts[k] for k in ix)
            a=F(c,r,m,t);v=F(c,r,m,(A0,)*len(t));z*=a
            ck(v-a >= int(len(set(t))>1)*F(c,r0,m-2,((1<<(p-1))-1,)*len(t)),'component loss')
            # Every elementary compression toward a smaller label (not
            # only the particular sorting sequence) is tested in each state.
            for i,j in combinations(I,2):
                u=tuple(shift(x,i,j) for x in t)
                ck(F(c,r,m,u)>=a,'nonmonotone sort');counts[2]+=1
        ck((Ppin==z)==stable and (Ppin-z)*den>=(not stable)*res,'pin');Z+=z;counts[1]+=1
    ck(fi==coef[p],'group fixed subsets')
    D=comb(m,p)*Ppin-Z
    ck(D*den>=(comb(m,p)-fi)*res,'total deficit')
    if max(orbits)>=3:ck(D>=3*res,'orbit triple')
    if all(all(x==p for x in r) for r in rs):
        ck(Z==fi and Ppin==1 and D*den==(comb(m,p)-fi)*res,'saturation');counts[3]+=1
    counts[0]+=1;counts[4]+=int(den>1)
    return (comb(m,p)*Ppin,Z,res,(comb(m,p)-fi),den)
for c in (star2,star3):
    # M=2,3 all connected tree cores below, all canonical gauges on hub
    # edges and all positive feasible inclusion ranks.
    for m in (2,3):
        I=tuple(range(m));per=tuple(permutations(I))
        for p in range(1,m):
            for r in product(range(1,m),repeat=c[0]):
                if any(r[l]>r[h] for l,h in c[1]) or any(r[w]<p for w in c[2]):continue
                for ps in product(per,repeat=len(c[2])-1):
                    case((c,),m,p,(r,),(I,)+ps)
for t in range(160):
    cc=RNG.choice(((p5,), (squaretail,), (star2,star2), (squaretail,twig)))
    m=RNG.choice((3,4,5));p=RNG.randrange(1,m);rs=[];pi=[]
    for c in cc:
        n,E,W=c;r=[RNG.randrange(1,m) for _ in range(n)]
        for w in W:r[w]=max(r[w],p)
        for l,h in E:r[h]=max(r[l],r[h])
        if t%5==0:r=[p]*n
        rs.append(tuple(r))
        for w in W:
            g=list(range(m));RNG.shuffle(g);pi.append(tuple(g))
    case(cc,m,p,tuple(rs),tuple(pi))
# Klein group action on four labels: no common invariant 2-set although
# each individual nonidentity element fixes two 2-sets.
a=(1,0,3,2);b=(2,3,0,1);i=tuple(range(4))
ck(case((star3,),4,2,((2,2,2,2),),(i,a,b))==(6,0,2,6,2),'Klein action')
# Uniform *raw* a=1 is not the saturation condition: twisted C4 with leaf.
ck(case((star2,twig),3,1,((1,2,2),(2,)),((0,1,2),(1,0,2),(0,1,2)))==(36,32,1,2,1),'raw vs rank equality')
print('profiles, pinned states, individual two-label comparisons, saturated profiles, nonunit denominators:',*counts)
print('PASS sheet-polynomial counts, full holonomy group/fixed-subset counts, pinned and aggregate deficits')
print('Klein orbit example: ordinary 6, gained 0, reduced 2. Equal raw occupancy counterexample to universal sharpness: 36, 32, 1.')
