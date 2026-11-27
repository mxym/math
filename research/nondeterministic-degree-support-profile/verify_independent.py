#!/usr/bin/env python3
"""Independent exact grid check: fractional RREF and coloop isolation."""
from fractions import Fraction as Q
from itertools import product
from math import prod


def rref(rows, width):
    a = [list(map(Q,r)) for r in rows]
    k = 0
    pivots = []
    for j in range(width):
        i = next((i for i in range(k,len(a)) if a[i][j]), None)
        if i is None:
            continue
        a[i], a[k] = a[k],a[i]
        b = [v/a[k][j] for v in a[k]]
        a[k] = b
        for i in range(len(a)):
            if i != k and a[i][j]:
                c = a[i][j]
                a[i] = [u-c*v for u,v in zip(a[i],b)]
        pivots.append(j)
        k += 1
    return a[:k], pivots


def isolation(at_degree, inside):
    # A span contains e_j iff its unique RREF row with pivot j is e_j.
    for d, vectors in enumerate(at_degree):
        mat = [[row[x] for x in inside] for row in vectors]
        reduced,pivots = rref(mat,len(inside))
        if any(sum(bool(c) for c in v) == 1 for v in reduced):
            return d
    raise AssertionError("one-point interpolation should always succeed")


def exact_support(at_degree, inside, outside, t):
    vectors = at_degree[t]
    width = len(vectors)
    zero_constraints = [[row[x] for row in vectors] for x in outside]
    dim = len(rref(zero_constraints,width)[1])
    return all(len(rref(zero_constraints+[[row[x] for row in vectors]],width)[1])>dim
               for x in inside)


def check(grid, all_direct):
    D = sum(len(a)-1 for a in grid)
    xs = list(product(*grid))
    N = len(xs)
    exps = list(product(*(range(len(a)) for a in grid)))
    values = {e:[prod(xi**ei for xi,ei in zip(x,e)) for x in xs] for e in exps}
    at_degree = [[values[e] for e in exps if sum(e) <= d] for d in range(D+1)]
    weights = [Q(1,prod(xi-y for axis,xi in zip(grid,x) for y in axis if xi != y))
               for x in xs]
    tests = 0
    for d in range(D):
        left,right = at_degree[d],at_degree[D-d-1]
        assert len(left)+len(right)==N
        for u in left:
            for v in right:
                assert sum(w*a*b for w,a,b in zip(weights,u,v))==0
                tests+=1

    lows = []
    essential_minima = []
    for d in range(D+1):
        # Construct actual minimum-word candidates by choosing a root
        # subset in every coordinate. Kept separate from the rank test.
        words = set()
        low = N+1
        for roots in product(*[range(1<<len(a)) for a in grid]):
            if (sum(r.bit_count() for r in roots) > d or
                    any(m.bit_count() == len(a) for m,a in zip(roots,grid))):
                continue
            term = [prod(xi-y for axis,xi,mask in zip(grid,x,roots)
                         for j,y in enumerate(axis) if (mask>>j)&1) for x in xs]
            support = sum(1<<j for j,u in enumerate(term) if u)
            if support.bit_count() < low:
                low = support.bit_count()
                words.clear()
            if support.bit_count() == low:
                words.add(support)
        lows.append(low)
        essential_minima.append(words)
    maxima = [0]*(N+1)
    critical = [0]*(D+1)
    direct = 0
    for S in range(1,1<<N):
        inside = [x for x in range(N) if (S>>x)&1]
        outside = [x for x in range(N) if not ((S>>x)&1)]
        e = isolation(at_degree,inside)
        nd = D-e
        if all_direct or S % 7 == 0 or len(inside) in (1,N):
            assert exact_support(at_degree,inside,outside,nd)
            assert nd == 0 or not exact_support(at_degree,inside,outside,nd-1)
            direct += 1
        maxima[len(inside)] = max(maxima[len(inside)],nd)
        if len(outside)+1 == lows[e]:
            critical[nd]+=1
    assert maxima[1:] == [D-next(i for i,m in enumerate(lows) if m <= N-s+1)
                          for s in range(1,N+1)]
    # Product witnesses need not be all minimizers. Every punctured
    # product witness is therefore checked as a subset of extremizers.
    puncture_checks = 0
    total = (1<<N)-1
    for e,words in enumerate(essential_minima):
        supports = {total ^ (W ^ (1<<x)) for W in words for x in range(N) if (W>>x)&1}
        for S in supports:
            inside = [x for x in range(N) if (S>>x)&1]
            assert isolation(at_degree,inside)==e
            puncture_checks+=1
        assert len(supports)<=critical[D-e]
    print(f"grid {grid}: {tests} weighted products, {total} isolation ranks, {direct} direct support cross-checks")
    print(f"  L_e={lows}; exact maxima={maxima[1:]}; critical counts={list(critical)}; {puncture_checks} puncture checks")


check(((-1,3),(-2,0,4)),True)
check(((-3,-1,2),(-2,1,5)),False)
check(((0,1),(0,2),(1,2,7)),False)
print("independent nonbinary grid checks: PASS")
