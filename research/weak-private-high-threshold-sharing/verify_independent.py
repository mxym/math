#!/usr/bin/env python3
"""Enumerate the finite dealer traces and independent projection moments."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from operator import xor
from functools import reduce


def zsum(vals):
    return reduce(xor,vals,0)


def sets(n):
    return tuple(I for k in range(n+1) for I in combinations(range(n),k))


def atom(vals,idxs):
    return tuple(vals[i] for i in idxs)


def project(hist,seen):
    res=Counter()
    for x,m in hist.items():
        res[atom(x,seen)]+=m
    return res


def dealer(gs,Q,K):
    n=len(gs)
    col=lambda x:zsum(g[u] for g,u in zip(gs,x))
    for s in (0,1):
        hist=Counter()
        for pre in product(range(Q),repeat=n-2):
            y=zsum(pre)
            completions=[pre+(a,y^a) for a in range(Q)
                         if col(pre+(a,y^a))==s]
            assert completions
            for W in range(K):
                hist[completions[W%len(completions)]]+=1
        yield hist


def moments(H,alph,p):
    n=len(alph)
    allJ=sets(n)
    ff=Counter(H[0]);ff.subtract(H[1])
    gg=H[0]+H[1]
    assert all(abs(ff[x])==w for x,w in gg.items())
    mass=sum(v*v for v in ff.values())
    ET={}
    for J in allJ:
        show=[i for i in range(n) if i not in J]
        norm=prod(alph[i] for i in J)
        vF=project(ff,show)
        vG=project(gg,show)
        nF=sum(f*f for f in vF.values())
        nG=sum(f*f for f in vG.values())
        ET[J]=F(nF,mass*norm)
        assert nG<=mass*norm
        if len(J)==1:
            assert ET[J]>=F(1,alph[J[0]])
        if len(J)==2:
            eps=(1-p)/(1+p)
            assert all(abs(vF[k])<=eps*g for k,g in vG.items())
            assert ET[J]<=eps**2
    eig={}
    for I in allJ:
        eig[I]=sum((-1)**(len(J)-len(I))*w for J,w in ET.items()
                   if set(I).issubset(J))
        assert eig[I]>=0
    assert sum(eig.values())==1
    mu=sum(len(I)*w for I,w in eig.items())
    mu2=sum(len(I)*(len(I)-1)*w for I,w in eig.items())
    assert mu==sum(v for J,v in ET.items() if len(J)==1)
    assert mu2==2*sum(v for J,v in ET.items() if len(J)==2)
    assert mu2>=mu*mu-mu
    a=sum(F(1,q) for q in alph)
    if a>=1:
        assert a*a-a<=n*(n-1)*((1-p)/(1+p))**2
    return len(allJ)


def fixture(Q,words,L,U,K):
    gs=tuple(tuple(int(i in a) for i in range(Q)) for a in words)
    n=len(gs)
    ds=lambda a,b,w:sum(a[i]!=b[i^w] for i in range(Q))
    assert all(L<=ds(a,b,w)<=U for (a,b),w in product(combinations(gs,2),range(Q)))
    totals=K*Q**(n-2)
    H=tuple(dealer(gs,Q,K))
    assert all(sum(V.values())==totals for V in H)
    assert not set(H[0]).intersection(H[1])
    cons=0
    for I in sets(n):
        P,R=(project(V,I) for V in H)
        if len(I)>=n-1:
            assert not set(P).intersection(R)
            for s,V in enumerate(H):
                for w in V:
                    given=atom(w,I)
                    x=dict(zip(I,given))
                    if len(I)<n: x[next(i for i in range(n) if i not in x)]=zsum(given)
                    assert zsum(gs[i][x[i]] for i in range(n))==s
                    cons+=1
    p=F(1)
    count=0
    ideal=F(L,U)*F(K//U,-((-K)//L))
    for I in sets(n):
        if len(I)>n-2: continue
        P,R=(project(V,I) for V in H)
        assert set(P)==set(R)
        if len(I)==n-2:
            assert len(P)==Q**len(I)
        for view in P:
            actual=F(min(P[view],R[view]),max(P[view],R[view]))
            assert actual>=ideal
            p=min(p,actual)
            count+=1
    checks=moments(H,(Q,)*n,p) + moments(H,tuple(Q+i%3 for i in range(n)),p)
    return count,cons,checks,p


def main():
    chars=[tuple(x for x in range(4) if (x&u).bit_count()%2) for u in (1,2,3)]
    q4=[(),(0,),*chars]
    q8=[(),(0,1,2)]+[tuple(x for x in range(8) if (x&u).bit_count()%2) for u in (1,2,3)]
    all_cases=[
        fixture(4,q4,1,3,4), fixture(4,q4,1,3,16),
        fixture(8,q8,3,5,64), fixture(4,[(),*chars],2,2,16)]
    assert all_cases[-1][-1]==1 and all_cases[0][-1]<1
    print(f"independent PASS: {sum(r[0] for r in all_cases)} direct view-ratio checks and {sum(r[1] for r in all_cases)} exact reconstructions")
    print(f"independent PASS: {sum(r[2] for r in all_cases)} equal/unequal-alphabet projection eigenweights, including perfect endpoint")
    # A mod sampler with 3 completions is not uniform; repeating an
    # identical local table creates a constant color in the zero-sum fiber.
    assert tuple(Counter(i%3 for i in range(4)).values())==(2,1,1)
    g=(0,1,1,0)
    assert set(g[u]^g[u] for u in range(4))=={0}
    for x in product(range(2),repeat=3):
        assert tuple(v^a^b for v,a,b in zip(x,(1,1,0),(0,1,1)))==tuple(v^a for v,a in zip(x,(1,0,1)))
    print("independent PASS: nonuniform-residue, duplicated-table, and binary double-flip controls")


if __name__=="__main__":
    main()
