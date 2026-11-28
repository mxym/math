#!/usr/bin/env python3
"""Exact tiny-table tests of product separation and algebraic zero tests."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
from math import gcd, lcm, prod
from random import Random


@lru_cache(None)
def points(moduli):
    return tuple(product(*(range(d) for d in moduli)))


def where(A,H,x):
    return tuple(sum(a*b for a,b in zip(row,x))%h for row,h in zip(A,H))


def phase(F,u,x):
    return sum((Q(a*b,m) for a,b,m in zip(u,x,F)),Q(0))%1


def order(F,u):
    return lcm(*(m//gcd(m,c) for m,c in zip(F,u)))


def pull(G,H,A,u):
    return tuple(int((g*sum((Q(a*b,h) for a,b,h in zip(u,col,H)),Q(0)))%g)
                 for g,col in zip(G,zip(*A)))


def mobius(n):
    s=1
    k=2
    while k*k<=n:
        if n%k==0:
            n//=k
            s=-s
            if n%k==0:
                return 0
        k+=1
    return -s if n>1 else s


@lru_cache(None)
def ram(h,k):
    g=gcd(h,k)
    return sum(d*mobius(h//d) for d in range(1,g+1) if g%d==0)


def prod_check(terms):
    E=defaultdict(int)
    for u,e in terms:
        u=Q(u)
        if u.numerator>1:
            E[u.numerator]+=e
        if u.denominator>1:
            E[u.denominator]-=e
    while True:
        found=False
        for a,b in combinations(sorted(E),2):
            g=gcd(a,b)
            if g==1:
                continue
            x,y=E.pop(a),E.pop(b)
            E[g]+=x+y
            if a>g:
                E[a//g]+=x
            if b>g:
                E[b//g]+=y
            found=True
            break
        if not found:
            return all(x==0 for x in E.values())


def candidate_entries(G,factors):
    d=defaultdict(list)
    for H,A,w in factors:
        for u in points(H):
            g=pull(G,H,A,u)
            if any(g):
                d[g].append((H,u,w))
    return d


def active(G,factors):
    d=candidate_entries(G,factors)
    used=set()
    out=[]
    for g,L in sorted(d.items()):
        if g in used:
            continue
        h=order(G,g)
        used.update(tuple((a*c)%m for m,c in zip(G,g))
                    for a in range(1,h) if gcd(a,h)==1)
        D=lcm(*(prod(H) for H,u,w in L))
        info=[]
        for H,u,w in L:
            for y in points(H):
                b=h*phase(H,u,y)
                assert b.denominator==1
                info.append((w[y],D//prod(H),int(b)))
        assert len(info)<=sum(len(w) for H,A,w in factors)
        if not all(prod_check((val,d0*ram(h,(j-b)%h)) for val,d0,b in info)
                   for j in range(h)):
            out.append(g)
    assert used==set(d)
    return out


def set_parts(n):
    if n==0:
        yield ()
        return
    for P in set_parts(n-1):
        yield P+((n-1,),)
        for j in range(len(P)):
            yield P[:j]+(P[j]+(n-1,),)+P[j+1:]


def singleton_anchored_product(W,G,P):
    w0=W[(0,)*len(G)]
    for x,v in W.items():
        if v*w0**(len(P)-1)!=prod(
            (W[tuple(x[j] if j in B else 0 for j in range(len(G)))] for B in P),start=Q(1)):
            return False
    return True


def support_fits(P,A):
    return all(any(all(not c or j in B for j,c in enumerate(a)) for B in P) for a in A)


def randfactor(G,H,R):
    for _ in range(300):
        A=tuple(tuple(R.randrange(gcd(g,h))*h//gcd(g,h) for g in G) for h in H)
        if {where(A,H,x) for x in points(G)}==set(points(H)):
            w={y:Q(R.randrange(1,10),R.randrange(1,10)) for y in points(H)}
            return (H,A,w)
    raise AssertionError((G,H))


def group_checks(R):
    trials=counts=0
    for G,shapes in (
        ((2,3),((2,),(3,),(6,))),
        ((4,6),((2,),(3,),(4,),(6,),(2,2),(2,3))),
        ((2,2,2),((2,),(2,2))),
        ((2,2,2,2),((2,),(2,2))),
        ((3,3,3),((3,),(3,3))),
        ((6,6),((2,),(3,),(6,),(2,3),(2,2))),
    ):
        for k in range(45):
            factors=[randfactor(G,R.choice(shapes),R) for _ in range(R.randrange(1,5))]
            if k%2==0:
                for H,A,w in factors[:(k%3+1)]:
                    factors.append((H,A,{x:1/y for x,y in w.items()}))
            A=active(G,factors)
            W={x:prod((w[where(L,H,x)] for H,L,w in factors),start=Q(1))
               for x in points(G)}
            for P in set_parts(len(G)):
                assert support_fits(P,A)==singleton_anchored_product(W,G,P)
                counts+=1
            trials+=1
    W={(z,):Q(2)**((-1)**z)*3**(z%3==0) for z in range(6)}
    A=active((6,),[((6,),((1,),),W)])
    assert {order((6,),u) for u in A}=={2,3}
    return trials,counts


def bigger_lcm_case():
    ps=(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)
    G=(2,)+ps
    Hs=[]
    for j,p in enumerate(ps,1):
        H=(2,p)
        A=tuple(tuple(int(i==h) for i in range(len(G))) for h in (0,j))
        w={(a,b):Q(10403)**(a if j%2 else -a) for a,b in points(H)}
        Hs.append((H,A,w))
    assert len(str(lcm(*(prod(H) for H,A,w in Hs))))>30
    assert active(G,Hs)==[]
    H,A,w=Hs[-1]
    Hs[-1]=(H,A,{(a,b):v*(2**a) for (a,b),v in w.items()})
    assert active(G,Hs)==[(1,)+(0,)*len(ps)]
    return len(ps)


def rank(A,p):
    piv={}
    for row in A:
        a=list(row)
        for j in range(len(a)):
            if a[j]==0:
                continue
            if j not in piv:
                piv[j]=[v*pow(a[j],-1,p)%p for v in a]
                break
            a=[(x-a[j]*y)%p for x,y in zip(a,piv[j])]
    return len(piv)


def basis_coeff(A,p):
    pows=points((p,)*len(A))
    return {tuple(sum(a*v[j] for a,v in zip(c,A))%p for j in range(len(A[0]))):c
            for c in pows}


def parts_from_basis(A,p):
    B=[]
    for v in A:
        if rank(B+[v],p)>len(B):
            B.append(v)
    cls=[{j} for j in range(len(B))]
    t=basis_coeff(B,p)
    for v in A:
        use={j for j,c in enumerate(t[v]) if c}
        cls=[C for C in cls if use.isdisjoint(C)]+[set().union(
             use,*(C for C in cls if not use.isdisjoint(C)))]
    return tuple(tuple(i for i,v in enumerate(A) if
                       all(not c or j in C for j,c in enumerate(t[v]))) for C in cls)


def intrinsic_checks(R):
    ntest=npart=0
    for p in (2,3):
        cand=[v for v in points((p,p,p)) if any(v) and next(x for x in v if x)==1]
        if p==2:
            tests=[tuple(v for j,v in enumerate(cand) if mask>>j&1)
                   for mask in range(1,1<<len(cand))]
        else:
            tests=[tuple(R.sample(cand,R.randrange(1,8))) for _ in range(42)]
        for A in tests:
            P=parts_from_basis(A,p)
            r=rank(A,p)
            assert sum(rank([A[i] for i in C],p) for C in P)==r
            assert sorted(i for C in P for i in C)==list(range(len(A)))
            for J in set_parts(len(A)):
                if sum(rank([A[i] for i in C],p) for C in J)==r:
                    assert all(any(set(B)<=set(C) for C in J) for B in P)
                npart+=1
            ntest+=1
    return ntest,npart


def pow_tests(R):
    n=0
    primes=(2,3,5,7)
    for _ in range(300):
        vec=[0]*len(primes)
        vals=[]
        for i in range(R.randrange(1,16)):
            a=tuple(R.randrange(-4,5) for p in primes)
            e=R.randrange(-10**50,10**50)
            vals.append((prod((Q(p)**a0 for p,a0 in zip(primes,a)),start=Q(1)),e))
            vec=[v+e*a0 for v,a0 in zip(vec,a)]
        vals+=list(zip(primes,(-v for v in vec)))
        assert prod_check(vals)
        vals[0]=(vals[0][0]*11,vals[0][1] or 1)
        assert not prod_check(vals)
        n+=2
    return n


def main():
    R=Random(4479152)
    print("PASS products / partitions / large-lcm target tables / intrinsic / powers:",
          *group_checks(R),bigger_lcm_case(),*intrinsic_checks(R),pow_tests(R))


if __name__=="__main__":
    main()
