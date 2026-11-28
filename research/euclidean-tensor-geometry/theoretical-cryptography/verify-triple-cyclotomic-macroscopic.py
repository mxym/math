#!/usr/bin/env python3
"""Exact small-array and scalar certificates for the three-factor theta."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod
from random import Random


def trace_coefficients(shape, bound=8):
    """Constant Laurent terms in (5) through a^8, with phase exponents."""
    a,b,c=shape
    triples=list(product(range(a),range(b),range(c)))
    count=Counter({0:1})
    # Any array in the line lattice has support >= 8. Thus through a^8
    # the only possible nonzero entries in a surviving monomial are ±1.
    for m in range(1,bound+1):
        for S in combinations(triples,m):
            # Test necessary degree parity before looping signs.
            P=Counter()
            for i,j,k in S:
                P[(0,i,j)]+=1
                P[(1,j,k)]+=1
                P[(2,k,i)]+=1
            if any(v%2 for v in P.values()):
                continue
            for signs in product((-1,1),repeat=m):
                Q=Counter()
                for (i,j,k),z in zip(S,signs):
                    Q[(0,i,j)]+=z
                    Q[(1,j,k)]+=z
                    Q[(2,k,i)]+=z
                if all(v==0 for v in Q.values()):
                    count[m]+=1
    return count


def native_grid(shape, bound=8):
    a,b,c=shape
    interior=list(product(range(a-1),range(b-1),range(c-1)))
    count=Counter()
    for vals in product((-1,0,1),repeat=len(interior)):
        X=Counter()
        for (i,j,k),z in zip(interior,vals):
            if z:
                for mask in product((0,1),repeat=3):
                    ii,jj,kk=(a-1 if mask[0] else i,
                              b-1 if mask[1] else j,
                              c-1 if mask[2] else k)
                    X[ii,jj,kk]+=(-1)**sum(mask)*z
        E=sum(v*v for v in X.values())
        if E<=bound:
            count[E]+=1
    return count


def direct_matrix_trials():
    r=Random(82)
    count=0
    for a,b,c in ((2,2,2),(2,3,2),(2,4,3),(4,2,3)):
        for _ in range(75):
            A=[[r.randrange(-3,4) for j in range(b)] for i in range(a)]
            B=[[r.randrange(-3,4) for k in range(c)] for j in range(b)]
            C=[[r.randrange(-3,4) for i in range(a)] for k in range(c)]
            tr=sum(A[i][j]*B[j][k]*C[k][i]
                   for i,j,k in product(range(a),range(b),range(c)))
            assert tr**2 <= prod(sum(u*u for row in D for u in row)
                                 for D in (A,B,C))
            count+=1
    return count


def compare_tensor_grams():
    count = 0
    for pp in ((3,5,7),(3,7,11)):
        M=prod(pp)
        for diffs in product(*(range(2-p,p-1) for p in pp)):
            d=sum((M//p)*v for p,v in zip(pp,diffs))
            # Ramanujan trace by independent inclusion-exclusion of
            # primitive embeddings in the full set of M-th roots.
            U=0
            for mask in product((0,1),repeat=3):
                t=prod(p for p,take in zip(pp,mask) if take)
                U+=(-1)**(3-sum(mask))*t*int(d%t==0)
            assert U == prod(p*int(v==0)-1 for p,v in zip(pp,diffs))
            count+=1
    return count


def log_interval(x, K=76):
    assert x>=1
    z=(x-1)/(x+1)
    X=F(0)
    power=z
    for j in range(K):
        X+=2*power/(2*j+1)
        power*=z*z
    return (X, X+2*power/((2*K+1)*(1-z*z)))


def circle_at(t, K=22):
    x=t*t/4
    a=F(1)
    A=F(1)
    B=F(0)
    for k in range(1,K+1):
        a*=x/k**2
        A+=a
        B+=k*a
    k=K+1
    next_a=a*x/(k*k)
    Ahi=A+next_a/(1-x/(k+1)**2)
    Bhi=B+(k*next_a)/(1-x/(k*(k+1)))
    llo=log_interval(A)[0]
    lhi=log_interval(Ahi)[1]
    rlo=2*B/(t*Ahi)
    rhi=2*Bhi/(t*A)
    return llo,lhi,rlo,rhi


def bound_scalar():
    tlo=F(32614221,10**7)
    thi=F(32614223,10**7)
    Llo,Lhi,rlo,rhi=circle_at(tlo)
    assert 3*Lhi-2*tlo*rlo<0
    Llo,Lhi,slo,shi=circle_at(thi)
    assert 3*Llo-2*thi*shi>0
    l=tlo/(2*shi*shi)
    h=thi/(2*rlo*rlo)
    assert F(23808873,10**7) < l < h < F(23808877,10**7)
    assert F(827596,10**6) < rlo < shi < F(827599,10**6)
    return float(l),float(h)


def main():
    shell=0
    for shape in ((2,2,2),(2,2,3),(2,3,3),(3,3,3)):
        D=native_grid(shape)
        n=2*prod(comb(x,2) for x in shape)
        assert D==Counter({0:1,8:n})
        if prod(shape)<=12:
            assert trace_coefficients(shape)==D
        shell+=n
    l,h=bound_scalar()
    print(f"PASS: {shell} exact shortest vectors in four boxes, "
          f"{direct_matrix_trials()} trace inequalities, "
          f"{compare_tensor_grams()} trace-Gram entries, "
          f"and rigorous c* in ({l:.9f},{h:.9f}).")


if __name__=="__main__":
    main()
