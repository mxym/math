#!/usr/bin/env python3
"""Exact toy verification of dyadic subfield identities. Requires SymPy."""
from itertools import product
from functools import lru_cache
from warnings import filterwarnings
import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

filterwarnings("ignore", category=SymPyDeprecationWarning)
x = sp.Symbol("x")


def rank(rows, p):
    a = [list(r) for r in rows]
    if not a:
        return 0
    k = 0
    for c in range(len(a[0])):
        j = next((j for j in range(k, len(a)) if a[j][c] % p), None)
        if j is None:
            continue
        a[k], a[j] = a[j], a[k]
        z = pow(a[k][c] % p, -1, p)
        a[k] = [(z * v) % p for v in a[k]]
        for i in range(k + 1, len(a)):
            if a[i][c] % p:
                z = a[i][c] % p
                a[i] = [(v-z*w) % p for v,w in zip(a[i],a[k])]
        k += 1
        if k == len(a):
            break
    return k


def order(p, modulus):
    y = p % modulus
    k = 1
    while y != 1:
        y = y*p % modulus
        k += 1
    return k


@lru_cache(None)
def irreducible_factors(n,p):
    factors = sp.factor_list(x**n+1,x,modulus=p)[1]
    out = []
    for poly, e in factors:
        h = tuple(int(v)%p for v in reversed(sp.Poly(poly,x).all_coeffs()))
        assert e == 1 and h[-1] == 1
        out.append(h)
    return out


def field_powers(h,p,through):
    f = len(h)-1
    a = (1,) + (0,)*(f-1)
    out = [a]
    for _ in range(through):
        a = tuple((v-a[-1]*c)%p for v,c in zip((0,)+a[:-1],h[:-1]))
        out.append(a)
    return out


def linear_eval(z,rows,p):
    return tuple(sum(a*b for a,b in zip(z,cc))%p for cc in zip(*rows))


def centered(x,p):
    return (x + p//2) % p-p//2


towers = bases = norms = restricted = collisions = 0
seen_ext = False
for n in (2,4,8,16,32):
    for p in (3,5,7,11,17,29,31,41,61,97,281):
        for h in irreducible_factors(n,p):
            f = len(h)-1
            a = field_powers(h,p,2*n)
            one = (1,) + (0,)*(f-1)
            minus_one = (p-1,) + (0,)*(f-1)
            assert a[n] == minus_one and a[2*n] == one
            assert f == order(p,2*n)
            q = p**f
            assert q % (2*n) == 1
            m = 1
            while m <= n:
                d = n//m
                beta = [a[d*j] for j in range(m)]
                fm = order(p,2*m)
                qm = p**fm
                assert rank(beta,p) == fm
                ell = f//fm
                assert f % fm == 0 and d % ell == 0 and q == qm**ell
                assert rank(beta[:fm],p) == fm
                if m < n:
                    assert order(p,4*m) in (fm,2*fm)
                towers += 1
                for start in range(0,d,ell):
                    rows = [a[i+d*j] for i in range(start,start+ell) for j in range(fm)]
                    assert rank(rows,p) == f
                    bases += 1
                # Exact phase-norm check in the standalone smaller field,
                # with rational inequality cleared by p^(2m).
                if qm <= 1100:
                    for hm in irreducible_factors(m,p):
                        assert len(hm)-1 == fm
                        b = field_powers(hm,p,m-1)
                        for z in product(range(p),repeat=fm):
                            if not any(z):
                                continue
                            S = sum(centered(sum(v*w for v,w in zip(z,bj)),p)**2 for bj in b)
                            assert qm**2*S**m >= p**(2*m)
                            norms += 1
                    # For small entire F, check each nonzero character
                    # has a nontrivial restriction in each basis group.
                    if q <= 320:
                        for z in product(range(p),repeat=f):
                            if not any(z):
                                continue
                            count = 0
                            for i in range(d):
                                count += any(sum(v*w for v,w in zip(z,a[i+d*j]))%p
                                             for j in range(m))
                            assert count*ell >= d
                            restricted += 1
                # Small radius boxes for which the AM-GM norm bound
                # supplies injection, tested jointly in ell independent blocks.
                if m*ell <= 8 and (4*m)**m < qm**2:
                    selected = [a[i+d*j] for i in range(ell) for j in range(m)]
                    if ell > 1 and m > 1:
                        seen_ext = True
                    images = {linear_eval(z,selected,p)
                              for z in product((-1,0,1),repeat=m*ell)}
                    assert len(images) == 3**(m*ell)
                    collisions += 1
                m *= 2
assert seen_ext

repairs = 0
for p in (2,3):
    for j in (1,2,3):
        # Exhaust all first j-1 rows of a j-square for j<=3 (and j=3,p=2);
        # direct rank-loss/repair counts give an independent local check.
        if j == 3 and p == 3:
            continue
        for flat in product(range(p),repeat=(j-1)*j):
            top = [flat[k*j:(k+1)*j] for k in range(j-1)]
            if rank(top,p) != j-1:
                continue
            zeros = 0
            for row in product(range(p),repeat=j):
                A = top+[row]
                if rank(A,p) == j:
                    continue
                zeros += 1
                for fresh_top in product(range(p),repeat=j-1):
                    losses = 0
                    for v in range(p):
                        cols = [rr+(w,) for rr,w in zip(A,fresh_top+(v,))]
                        losses += rank(cols,p) < j
                    assert losses == 1
                    repairs += 1
            assert zeros == p**(j-1)

# Leading and medium cutoffs are in the advertised order, and the two
# estimate scales are ordered across a range of growing dimensions.
from math import exp, log, pi, sqrt
a0 = 2*exp(-2)
b0 = sqrt(a0/2)
for h in range(8,100):
    n = 2**h
    L = log(4*n*n)
    for delta in (0.01,0.10,0.25,0.40,0.49,0.75):
        lam = min(exp(-pi),n**(-delta))
        E = lam*sqrt(n/L)
        assert b0*sqrt(lam*n) <= sqrt(n*L) <= n
        assert sqrt(lam*n) >= E
        assert b0*sqrt(lam*n) - a0*lam*n/(b0*sqrt(lam*n)) <= -b0*sqrt(lam*n)+1e-10*sqrt(lam*n)

print("PASS tower datasets",towers,"basis blocks",bases)
print("PASS exact phase lower bounds",norms,"character restrictions",restricted)
print("PASS exact joint-box injections",collisions,"fresh-coordinate repair tests",repairs)
