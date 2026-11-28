#!/usr/bin/env python3
"""Finite arithmetic checks for Gaussian location transport obstructions."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import factorial, gcd


def add(a, b, q):
    return tuple((u+v) % q for u, v in zip(a, b))


def neighbors(x, q):
    d = len(x)
    return {add(x, tuple(s*(i==j) for i in range(d)), q)
            for j in range(d) for s in (-1, 1)}


def graph(q, d, enumerate_all=False):
    points = list(product(range(q), repeat=d))
    ix = {x:i for i,x in enumerate(points)}
    adj = [set(ix[y] for y in neighbors(x,q)) for x in points]
    pairs = 0
    for i,x in enumerate(points):
        for j in adj[i]:
            for k in adj[i]:
                if j >= k:
                    continue
                y, z = points[j], points[k]
                same = sum(a!=b for a,b in zip(y,z)) == 1
                common = adj[j] & adj[k]
                assert i in common
                assert len(common) == (1 if same else 2)
                pairs += 1
    successes = 0
    if enumerate_all:
        edges = [(i,j) for i,v in enumerate(adj) for j in v if i<j]
        for pi in permutations(range(len(points))):
            if all(pi[j] in adj[pi[i]] for i,j in edges):
                successes += 1
        assert successes == q**d*factorial(d)*2**d
    return pairs, successes


def check_short_arcs(q):
    m = 14*q
    ticks = [14*i for i in range(q)]
    def dist(x,y):
        a = (x-y) % m
        return min(a,m-a)
    for x in range(m):
        i,j = sorted(range(q), key=lambda i: (dist(x,ticks[i]),i))[:2]
        if (j-i)%q == q-1:
            i,j = j,i
        assert (j-i)%q == 1
        assert (x-ticks[i])%m <= 14
        assert dist(x,ticks[i]) + dist(x,ticks[j]) == 14
    return m


def make_phi_power(q):
    # The synthetic moduli here are primes or 9.
    if q == 9:
        return (1,0,0,1,0,0,1)
    return tuple(1 for i in range(q))


def zero_sum_pow(counts, q):
    phi = make_phi_power(q)
    dg = len(phi)-1
    counts = counts.copy()
    for k in range(q-1,dg-1,-1):
        c = counts[k]
        for j,x in enumerate(phi):
            counts[k-dg+j] -= c*x
    return not any(counts)


def axis_supported(q, d, vals, pts):
    axes = {v for v in pts if sum(t!=0 for t in v)==1 and
            any(t in (1,q-1) for t in v)}
    for v in pts:
        if v in axes:
            continue
        coeffs = Counter((sum(a*b for a,b in zip(v,h))-y)%q
                         for h,y in zip(pts,vals))
        if not zero_sum_pow([coeffs[i] for i in range(q)],q):
            return False
    return True


def finite_support(q,d):
    pts = list(product(range(q),repeat=d))
    if d == 1:
        candidates = permutations(range(q))
    else:
        assert q == 3 and d == 2
        candidates = sorted(set(permutations(tuple(i for i in range(q)
                                                     for j in range(q)))))
    total = linear = 0
    for vals in candidates:
        found = axis_supported(q,d,vals,pts)
        expect = any(all(y==(s*h[i]+c)%q for y,h in zip(vals,pts))
                     for i in range(d) for c in range(q) for s in (-1,1))
        assert found == expect
        total += 1
        linear += found
    assert linear == 2*d*q
    return total


def affine_distortion(q):
    nonzero = [v for v in product(range(q),repeat=2) if any(v)]
    def sq(v):
        return sum(min(x%q,-x%q)**2 for x in v)
    norms = {v:sq(v) for v in nonzero}
    count = 0
    shear = None
    eq = 0
    for a,b,c,e in product(range(q),repeat=4):
        if gcd(a*e-b*c,q) != 1:
            continue
        rn,rd = 1,1
        for x,y in nonzero:
            m0 = norms[x,y]
            m1 = sq((a*x+c*y,b*x+e*y))
            if m1*rd > m0*rn:
                rn,rd = m1,m0
        signed_perm = sq((a,b))==sq((c,e))==1
        assert (rn==rd) == signed_perm
        eq += signed_perm
        if (a,b,c,e)==(1,1,0,1):
            shear = Fraction(rn,rd)
        count += 1
    assert eq == 8
    assert shear >= (Fraction(5,2) if q>=5 else 2)
    return count, shear


def main():
    ps = ns = 0
    for q,d in ((3,1),(3,2),(3,3),(5,1),(5,2),(5,3),(7,1),(7,2),(9,2)):
        p,n = graph(q,d,(d==1 and q<=7) or (q,d)==(3,2))
        ps += p
        ns += n
    print("PASS graph local pairs / full counted automorphisms:", ps, ns)
    print("PASS circle short-arc rows:", sum(map(check_short_arcs,(3,5,7,9,15))))
    print("PASS balanced Fourier-support tables:",
          sum(finite_support(q,d) for q,d in ((3,2),(5,1),(7,1))))
    ans = [affine_distortion(q) for q in (3,5,7,9)]
    print("PASS invertible affine frequency tables:", sum(n for n,v in ans))
    print("Shear beta:", ", ".join(str(v) for n,v in ans))


if __name__=="__main__":
    main()
