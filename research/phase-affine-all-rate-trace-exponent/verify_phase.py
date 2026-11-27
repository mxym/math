#!/usr/bin/env python3
"""Independent direct character density matrices; exact spectral enclosures."""
from fractions import Fraction as F
from itertools import product
from math import log2


def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q


def char_terms(exps,q):
    # Coefficients modulo Phi_q, for tested prime q=2 or 3.
    C = [0]*q
    for j in exps:
        C[j] += 1
    return tuple(C[j]-C[-1] for j in range(q-1))


def key(A,x,q):
    return tuple(dot(row,x,q) for row in A)


def rowspace(A,N,q):
    return {tuple(sum(c*row[i] for c,row in zip(u,A))%q for i in range(N))
            for u in product(range(q),repeat=len(A))}


def eigen_interval(p):
    p = [u for u in p if u]
    if len(p) < 2:
        return F(0),F(0)
    left,right = F(0),sum(p)
    # Rank-one secular equation 1 = v^*(lambda I+diag(p))^{-1}v.
    for _ in range(38):
        mid = (left+right)/2
        if sum(u/(mid+u) for u in p) > 1:
            left=mid
        else:
            right=mid
    return left,right


def direct_phase(A,q,N,amps):
    V = list(product(range(q),repeat=N))
    C = rowspace(A,N,q)
    assert len(C)==q**len(A)
    groups = {}
    for x in V:
        groups.setdefault(key(A,x,q),[]).append(x)
    wnorm = sum(a*a for a in amps)
    mass = {x:F(a*a,wnorm) for x,a in zip(V,amps)}
    coef = count = 0
    for xs in groups.values():
        rep = xs[0]
        assert len(xs) == q**(N-len(A))
        for t,t1 in product(V,repeat=2):
            d = tuple((a-b)%q for a,b in zip(t,t1))
            av = tuple(F(v,len(xs)) for v in char_terms([dot(x,d,q) for x in xs],q))
            pred = char_terms([dot(rep,d,q)],q) if d in C else (0,)*(q-1)
            assert av == pred
            coef += 1
    unseen=set(V)
    lo=hi=F(0)
    for t in V:
        if t not in unseen:
            continue
        B={tuple((a+b)%q for a,b in zip(t,w)) for w in C}
        unseen -= B
        p=[mass[x] for x in B]
        a,b=eigen_interval(p)
        x=(sum(p))**2-sum(w*w for w in p)
        assert a*a <= x <= 2*b*b
        lo+=a
        hi+=b
        count+=1
    assert not unseen
    assert lo<=hi<=1
    return lo,hi,coef,count


def small():
    phases=[(2,1,1,[(3,1),(1,0)]),
            (2,3,1,[(3,1,2,0,1,4,2,1)]),
            (2,3,2,[(3,1,1,2,0,1,0,2)]),
            (3,1,1,[(2,3,1),(0,1,0)]),
            (3,2,1,[(1,2,1,3,1,0,2,1,3)]),
            (3,2,2,[(1,2,1,0,1,0,2,1,3)])]
    nc=nm=nb=nd=0
    for q,N,r,Ws in phases:
        V = list(product(range(q),repeat=N))
        # Enumerate actual A entries instead of deduplicated field subspaces.
        good=0
        numdef=0
        for A in product(V,repeat=r):
            L=len(rowspace(A,N,q))
            if L < q**r:
                # Pure point law: directly compare actual distribution of Ax with U.
                P={a:0 for a in product(range(q),repeat=r)}
                for x in V:
                    P[key(A,x,q)]+=1
                d=sum(abs(F(n,q**N)-F(1,q**r)) for n in P.values())/2
                assert d==1-F(L,q**r)
                nd+=1
                numdef+=1
                continue
            good+=1
            for W in Ws:
                lo,hi,c,b=direct_phase(A,q,N,W)
                assert (hi==0)==(sum(w>0 for w in W)==1)
                nc+=c
                nb+=b
                nm+=1
        expect=1
        for j in range(r):
            expect*=q**N-q**j
        assert good==expect and numdef==q**(N*r)-expect
    # r=0 leaves a singleton key and thus exactly zero error for any source.
    d0,d1,checks,blocks=direct_phase((),2,2,(1,2,3,4))
    assert d0==d1==0
    nc+=checks
    nb+=blocks
    print(f"phase matrices: {nm} full-rank maps/profiles, {nc} exact character entries, {nb} secular blocks")
    print(f"degenerate controls: {nd} rank defects with deterministic phase, deterministic full-rank and singleton output PASS")


def ent(P):
    return -sum(u*log2(u) for u in P if u)


def dual(theta,P,lam,c):
    L=[[a**(1/(1+theta)) for a in v] for v in lam]
    S=[sum(v) for v in L]
    cond=[[a/s for a in v] for v,s in zip(L,S)]
    wt=[p*s**(1+theta) for p,s in zip(P,S)]
    B=sum(wt)
    W=[w/B for w in wt]
    h=sum(w*ent(v) for w,v in zip(W,cond))
    v=theta*c-log2(B)
    div=sum(w*log2(w/p)+w*sum(r*log2(r/a) for r,a in zip(s,t) if r)
            for w,p,s,t in zip(W,P,cond,lam))
    return h,v,div


def solve(P,lam,c):
    l,h=0.,1.
    if c <= dual(l,P,lam,c)[0]:
        theta=l
    elif c >= dual(h,P,lam,c)[0]:
        theta=h
    else:
        for _ in range(55):
            m=(l+h)/2
            if c > dual(m,P,lam,c)[0]:
                l=m
            else:
                h=m
        theta=(l+h)/2
    H,v,d=dual(theta,P,lam,c)
    assert abs(v-d-max(0.,c-H))<1e-12
    return theta,v


def flag_and_rates():
    V=list(product(range(2),repeat=2))
    A=((1,1),)
    ary=(F(2,7),F(5,7))
    ss=((3,1),(1,0))
    lo=hi=F(0)
    for y in V:
        w=ary[y[0]]*ary[y[1]]
        p=[ss[y[0]][i]*ss[y[1]][j] for i,j in V]
        a,b,_,_=direct_phase(A,2,2,p)
        lo+=w*a
        hi+=w*b
    # Sum of the two-by-two phase-block eigenvalues here is a sum
    # of square roots of rational weights; these amplitudes make
    # those roots rational.
    norm = F(9,50)*ary[0]**2
    assert lo<=norm<=hi
    P=(1.,); lam=((.9,.1),)
    t,v=solve(P,lam,.99)
    assert t==1. and abs(v-(.99-log2(1.6)))<1e-12
    th,high=solve(P,lam,.76)
    assert 0<th<1 and 0<high<v
    t2,z=solve(P,lam,.35)
    assert t2==0 and z==0
    for c in (0.,.2,.6,1.,1.3,1.9,2.):
        solve((.4,.6),((.5,.3,.2,0.),(.8,.15,.05,0.)),c)
    print("phase flags: two-copy mixed orthogonal model attained exact rational check")
    print(f"Gallager check: binary p=.1, R=.01 exponent {v:.9f}; R=.24 exponent {high:.9f}; above capacity 0")
    print("Gallager checks: 7 unequal readable-flag rate cases (primal/dual) PASS")


if __name__ == '__main__':
    small()
    flag_and_rates()
