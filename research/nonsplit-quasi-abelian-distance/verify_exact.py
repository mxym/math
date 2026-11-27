#!/usr/bin/env python3
"""Exact counts for cube density, partial spreads and probability thresholds."""
from collections import Counter
from itertools import product


def space(r, m):
    return list(product(range(r), repeat=m))


def canon_cubes(r, m, d):
    V = space(r, m)
    index = {v: i for i, v in enumerate(V)}
    S = list(product(range(2),repeat=d))
    D = list(product(range(r),repeat=d))
    hist = Counter()
    dependent = 0
    for hs in product(V, repeat=d):
        def offset(coeff):
            return tuple(sum(t*h[j] for t,h in zip(coeff,hs))%r for j in range(m))
        offsets = {offset(e) for e in S}
        if len({offset(e) for e in D}) < r**d:
            dependent += len(V)
        for x in V:
            mask = sum(1 << index[tuple((a+b)%r for a,b in zip(x,y))] for y in offsets)
            hist[mask] += 1
    assert sum(hist.values()) == len(V)**(d+1)
    if d:
        assert dependent * len(V) < len(V)**(d+1) * r**d
    return hist


density_checks = masks = 0
for r,m in ((2,3),(3,2)):
    N = r**m
    for d in range(1,4 if r==2 else 3):
        H = canon_cubes(r,m,d)
        masks += len(H)
        for A in range(1<<N):
            hits = sum(w for M,w in H.items() if A&M==M)
            assert hits*N**(1<<d) >= N**(d+1)*A.bit_count()**(1<<d)
            density_checks += 1


def mul(a,b,r,coeff):
    # Minimal polynomial X^e + sum_i coeff[i] X^i.
    e = len(coeff)
    s = [0]*(2*e-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            s[i+j] += x*y
    for i in range(2*e-2,e-1,-1):
        for j,c in enumerate(coeff):
            s[i-e+j] -= s[i]*c
    return tuple(x%r for x in s[:e])


spreads = disjoint_points = 0
for r,P in ((2,(1,1)),(2,(1,1,0)),(3,(1,0)),(3,(2,2,0))):
    e = len(P)
    V = space(r,e)
    for a in V[1:]:
        assert len({mul(a,b,r,P) for b in V}) == r**e
    for d in range(1,e+1):
        U = space(r,d)[1:]
        used = set()
        for a in V:
            W = {u+mul(a,u+(0,)*(e-d),r,P) for u in U}
            assert len(W)==r**d-1 and not used&W
            used |= W
        assert len(used)==r**e*(r**d-1)
        spreads += 1
        disjoint_points += len(used)

tail_checks = 0
for q in (2,3,4,7,16,101):
    for r in (2,3,5,7):
        if q%r==0:
            continue
        for h in (1,2,7):
            for m in range(4,513):
                # Exact equivalent of r^d <= m log_q(r)/(4h).
                d=0
                while q**(4*h*r**(d+1)) <= r**m:
                    d+=1
                if not d or 4*d>m:
                    continue
                assert r**(m-d) >= r**(m//2) * q**(h*(r**d-1))
                # Rounding lower bound for r^d via the failed d+1 inequality.
                assert q**(4*h*r*r**d)>r**m
                tail_checks += 1

# The strict independence condition is not optional: any one-point A gives
# positive cube density with all directions zero but no nondegenerate cube.
assert canon_cubes(2,2,2)[1] == 1
print(f"PASS exact: {density_checks} density inequalities ({masks} corner masks); "
      f"{spreads} partial spreads, {disjoint_points} disjoint nonzeros; "
      f"{tail_checks} integer tail cutoffs; degenerate-cube control")
