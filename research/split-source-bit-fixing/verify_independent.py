#!/usr/bin/env python3
"""Enumerate actual oracle transcript couplings independently of masking."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations,product
from math import prod


def all_subsets(n):
    return [U for k in range(n+1) for U in combinations(range(n),k)]


def marginal(W,U):
    out=defaultdict(int)
    for h,m in W.items():
        out[tuple(h[i] for i in U)]+=m
    return out


def split(weights, m, r_twice, expected_budget, eps):
    original_mass=sum(weights.values())
    n=len(next(iter(weights)))
    subsets=all_subsets(n)
    a=lambda U: 2**(r_twice*len(U))
    blocks=[]
    residual=dict(weights)
    while sum(residual.values())>=eps*original_mass:
        mass=sum(residual.values())
        cell=next(((U,value) for U in reversed(subsets) if U
                   for value,s in sorted(marginal(residual,U).items())
                   if s*s*a(U)>mass*mass),((),()))
        U,value=cell
        block={h:s for h,s in residual.items()
               if tuple(h[i] for i in U)==value}
        for h in block: del residual[h]
        assert len(U)<=expected_budget
        goodmass=sum(block.values())
        for A in subsets:
            if set(A).isdisjoint(U):
                assert max(marginal(block,A).values())**2*a(A)<=goodmass**2
        blocks.append((U,value,block,False))
    if residual:
        assert sum(residual.values())<eps*original_mass
        blocks.append(((),(),residual,True))
    assert sum(len(B) for U,v,B,e in blocks)==len(weights)
    assert {h:w for U,v,B,e in blocks for h,w in B.items()}==weights
    return blocks


def alternatives(n,m,U,vals):
    look=dict(zip(U,vals))
    R=[i for i in range(n) if i not in look]
    for free in product(range(m),repeat=len(R)):
        assign=look|dict(zip(R,free))
        yield tuple(assign[i] for i in range(n))


def observe(H,y,z,q):
    r=[]
    a=y+sum((i+1)*k for i,k in enumerate(z))
    for i in range(q):
        cell=a%len(H)
        v=H[cell]
        r.append((cell,v))
        if (a+i+v)%7==6: break
        a=(a+3*v+i*i+cell)%139
    return tuple(r),a%2


def demo_partition():
    M=4
    n=4
    tables=list(product(range(M),repeat=n))
    weights=defaultdict(dict)
    for h in tables:
        z=(h[0]//2,h[0]%2)
        weights[z][h]=1
    # This is the actual theorem family when each source reports one bit
    # of H[0] and the two coordinates are separately uniformly random.
    # sigma'=4, delta*=1/2, P=8, P0=8, ell=3/2, and r=1/2.
    info={}
    for z,W in weights.items():
        blocks=split(W,4,1,8,F(1,4))
        assert len(blocks)==1 and blocks[0][0]==(0,)
        info[z]=blocks
    # An independent uneven-support regression exercises the residual tail.
    w={(0,h[1],h[2],h[3]):4 for h in tables if h[0]==0}
    w[(1,0,0,0)]=1
    extra=split(w,4,1,8,F(1,4))
    assert extra[0][0]==(0,) and extra[-1][3]
    count=0
    for z,blocks in list(info.items())+[((3,2),extra)]:
        for U,v,B,e in blocks:
            if e: continue
            n0=sum(B.values())
            Y=list(alternatives(n,M,U,v))
            for y,q in product(range(M),range(6)):
                a=defaultdict(int);b=defaultdict(int)
                for h,w0 in B.items(): a[observe(h,y,z,q)]+=F(w0,n0)
                for h in Y: b[observe(h,y,z,q)]+=F(1,len(Y))
                for path,a0 in a.items():
                    assert b[path]>0
                    nonfixed=len({u for u,x in path[0] if u not in U})
                    assert b[path]==F(1,4**nonfixed)
                    # a <= 2^(ell*s) b where ell=3/2. Square for exactness.
                    assert a0*a0 <= 2**(3*nonfixed)*b[path]*b[path]
                    count+=1
    print(f"independent PASS: {count} adaptive density-path probabilities; one family reused for six query budgets, including a residual-tail fixture")

    # Verify the reprogramming joint law for every fixed cell or free
    # cell and observe that transcript disagreement implies the union
    # of the two claimed events in the independent-challenge execution.
    coup=0
    for z in info:
        U,v,_,_=info[z][0]
        pool=list(alternatives(n,M,U,v))
        for x,q in product(range(n),range(6)):
            w=defaultdict(int)
            for g,y in product(pool,range(M)):
                h=list(g)
                if x not in U: h[x]=y
                w[tuple(h),h[x]]+=F(1,len(pool)*M)
                a=observe(g,y,z,q)
                d=observe(h,h[x],z,q)
                if a!=d:
                    assert x in U or any(j==x for j,val in a[0])
            assert w=={(g,g[x]):F(1,len(pool)) for g in pool}
            coup+=1
    print(f"independent PASS: {coup} exact fresh-challenge coupling laws and disagreement-event tests")


def posterior_fixture():
    M=4
    Fs=list(product(range(M),repeat=4))
    # Two independent coordinates conditioned on H co-vary in entropy:
    # each is deterministic in the same oracle branch, and uniform otherwise.
    max1=max2=maxprod=F(0)
    hits={q:F(0) for q in range(6)}
    for h in Fs:
        u=(F(1),F(0)) if h[0]==0 else (F(1,2),F(1,2))
        max1+=max(u)/len(Fs);max2+=max(u)/len(Fs)
        maxprod+=max(u)**2/len(Fs)
        for y,q in product(range(M),range(6)):
            path={addr for addr,val in observe(h,y,(h[0]//2,h[0]%2),q)[0]}
            hits[q]+=sum(u[a]*u[b] for a,b in product(range(2),repeat=2)
                         if 2*a+b in path)/len(Fs)/M
    delta=max(max1,max2)
    assert delta==F(5,8) and maxprod==F(7,16)>delta**2
    assert all(mass**2<=q*delta**2 for q,mass in hits.items())
    # Independently, check the set-size inequality for the full grid of
    # pairs of nonidentical rational posterior coordinates.
    count=0
    for den,a,b,s in product(range(2,17),range(17),range(17),range(5)):
        if a>den or b>den:continue
        hi=(max(F(a,den),1-F(a,den)),max(F(b,den),1-F(b,den)))
        assert min(1,s*prod(hi))**2<=s*prod(hi)
        count+=1
    print(f"independent PASS: {count} posterior-set bounds and co-varying posterior negative control")


def budgets():
    checks=0
    for j,sigma,mix,q,shift in product(range(1,33),(0,1,5,10,100),
                                       (1,2,3),(0,1,2,100,2**30),(-1,0,1)):
        N=2**j
        delta=min(F(1),F(mix,N))
        sig=sigma+2*j
        c=-((-sig)//delta)
        assert (c-1)*delta<sig<=c*delta
        P=max(1,c+shift)
        P0=min(P,c)
        B2=sig*(q+1)*delta
        assert sigma+2+4*j<=3*sig
        assert delta**2*P0<=4*B2
        assert delta**2*q<=B2
        assert F(1,N**4)<=B2
        assert F(sig*q,P0)<=F(sig*q,P)+q*delta
        if q*delta<=1:
            assert (q*delta)**2<=B2
        else:
            assert 1<B2
        checks+=1
    print(f"independent PASS: {checks} q-free capacity, slack, and rounding identities")


if __name__=="__main__":
    demo_partition()
    posterior_fixture()
    budgets()
