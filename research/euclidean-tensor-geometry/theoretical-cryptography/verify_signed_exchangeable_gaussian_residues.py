#!/usr/bin/env python3
"""Exact small checks of the residue decomposition and selected packing facts."""
from collections import Counter
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import combinations, product
from random import Random

rng=Random(657412)
res=Counter()


def signed_swap(Q,i,j,s):
    n=len(Q)
    pi=list(range(n))
    pi[i],pi[j]=j,i
    sig=[s if a in (i,j) else 1 for a in range(n)]
    return tuple(tuple(Q[pi[a]][pi[b]]*sig[a]*sig[b] for b in range(n)) for a in range(n))


def recognize(Q):
    n=len(Q)
    ok={}
    for i,j in combinations(range(n),2):
        s=next((s for s in (1,-1) if signed_swap(Q,i,j,s)==Q),None)
        if s is not None:
            ok[i,j]=s
    def same(a,b):
        return a==b or tuple(sorted((a,b))) in ok
    for i,j,k in product(range(n),repeat=3):
        assert not (same(i,j) and same(j,k)) or same(i,k)
        res["signed equivalence triples"]+=1
    unseen=set(range(n))
    groups=[]
    sig=[1]*n
    while unseen:
        a=min(unseen)
        g=[b for b in sorted(unseen) if same(a,b)]
        groups.append(tuple(g))
        unseen.difference_update(g)
        for b in g[1:]:
            sig[b]=ok[a,b]
    q=tuple(tuple(Q[i][j]*sig[i]*sig[j] for j in range(n)) for i in range(n))
    k=len(groups)
    enc=[next(a for a,g in enumerate(groups) if i in g) for i in range(n)]
    B=[[F(0)]*k for _ in range(k)]
    a=[]
    for i,g in enumerate(groups):
        B[i][i]=q[g[0]][g[1]] if len(g)>1 else q[g[0]][g[0]]-1
        a.append(q[g[0]][g[0]]-B[i][i])
        for j in range(i):
            B[i][j]=B[j][i]=q[g[0]][groups[j][0]]
    assert min(a)>0
    assert q == tuple(tuple(B[enc[i]][enc[j]]+a[enc[i]]*int(i==j)
                        for j in range(n)) for i in range(n))
    return groups,sig,a,B


def form(Q,x):
    return sum(Q[i][j]*x[i]*x[j] for i in range(len(x)) for j in range(len(x)))


def tiny_instance(ns):
    groups=[]
    j=0
    for n in ns:
        groups.append(tuple(range(j,j+n)))
        j+=n
    n=sum(ns)
    k=len(ns)
    L=[[F(rng.randrange(-12,13),rng.randrange(1,9)) if i>j else
        F(rng.randrange(1,12),rng.randrange(1,10)) if i==j else F(0)
        for j in range(k)] for i in range(k)]
    C=[[sum(L[i][t]*L[j][t] for t in range(k)) for j in range(k)] for i in range(k)]
    a=[F(rng.randrange(1,11),rng.randrange(1,11)) for i in range(k)]
    B=[[C[i][j]-int(i==j)*a[i]/ns[i] for j in range(k)] for i in range(k)]
    mix=rng.sample(range(n),n)
    enc=[next(i for i,g in enumerate(groups) if mix[j] in g) for j in range(n)]
    sig=[rng.choice((-1,1)) for i in range(n)]
    Q=tuple(tuple(sig[i]*sig[j]*B[enc[i]][enc[j]]+int(i==j)*a[enc[i]]
                  for j in range(n)) for i in range(n))
    groups,sig,a,B=recognize(Q)
    k=len(groups)
    ns=list(map(len,groups))
    C=[[B[i][j]+int(i==j)*a[i]/ns[i] for j in range(k)] for i in range(k)]
    return Q,groups,sig,a,B,C,ns


def fiber_counts(N,t,a):
    X=(-1,0,1,2)
    hist={(0,0):1}
    for _ in range(N):
        y=Counter()
        for (s,e),num in hist.items():
            for x in X:
                y[s+x,e+x*(x-1)]+=num
        hist=y
    bias=a*t*(1-F(t,N))
    cc=Counter({a*e+bias:w for (s,e),w in hist.items() if s==t})
    direct=Counter(a*sum((z-F(t,N))**2 for z in x)
                   for x in product(X,repeat=N) if sum(x)==t)
    assert min(cc)==bias and cc == direct
    res["local residue fibers"]+=1
    return cc


for ns in ((2,), (2,1),(2,2),(1,3),(4,),(1,1,2)):
    for _ in range(7):
        Q,gr,sg,a,B,C,ns0=tiny_instance(ns)
        d=len(gr)
        n=sum(ns)
        terms={}
        fcache=[{t:fiber_counts(N,t,b) for t in range(N)} for N,b in zip(ns0,a)]
        for t in product(*(range(x) for x in ns0)):
            v={F(0):1}
            for i,c in enumerate(t):
                z=Counter()
                for e,b in v.items():
                    for h,w in fcache[i][c].items():
                        z[e+h]+=b*w
                v=z
            th=Counter()
            for r in product((-1,0,1),repeat=d):
                y=[a*N+b for a,N,b in zip(r,ns0,t)]
                gs=form(C,y)
                for e,w in v.items():
                    th[gs+e]+=w
            terms[t]=th
        brute={t:Counter() for t in terms}
        for y in product(range(-2,4),repeat=n):
            bs=[sum(y[i] for i in g) for g in gr]
            t=tuple(x%N for x,N in zip(bs,ns0))
            r=[(x-c)//N for x,c,N in zip(bs,t,ns0)]
            if any(abs(v)>1 for v in r):
                continue
            if any(not -1<=y[i]-r[j]<=2 for j,g in enumerate(gr) for i in g):
                continue
            x=[a*b for a,b in zip(y,sg)]
            brute[t][form(Q,x)]+=1
            res["direct energy rows"]+=1
        assert terms==brute
        res["full residue instances"]+=1

for d in range(2,7):
    reps={}
    for z in product(range(-1,3),repeat=d):
        mean=F(sum(z),d)
        shift=(mean+F(1,2)).__floor__()
        u=tuple(x-shift for x in z)
        assert -F(1,2)<=F(sum(u),d)<F(1,2)
        w=tuple(x-mean for x in z)
        assert 4*sum(x*x for x in w)>=sum(x*x for x in u)
        if w in reps:
            assert reps[w]==u
        else:
            reps[w]=u
        res["dual representative checks"]+=1
    assert reps[(F(0),)*d]==(0,)*d

# Validate the constant of the fixed-dimensional partial Poisson factor
# with an independent finite rectangular sum and a genuinely shifted shear.
with localcontext() as ctx:
    ctx.prec=70
    PI=D("3.141592653589793238462643383279502884197169399375105820974944592")
    A=D("0.12")
    B=D("2")
    for v in ("0.19","-0.32","0.41"):
        for u in ("-0.1","0.23"):
            v0,u0=D(v),D(u)
            total=0
            projection=0
            for y in range(-9,10):
                z=y-v0
                q=(-B*z*z).exp()
                projection+=q
                cen=u0+D("0.41")*z
                near=int(cen.to_integral_value())
                local=sum((-A*(x-cen)**2).exp() for x in range(near-45,near+46))
                total+=q*local
            rel=abs(total/(projection*(PI/A).sqrt())-1)
            assert rel<D("1e-32")
            res["shifted partial Poisson checks"]+=1
print("PASS exchangeable Gaussian residues:",dict(res))
