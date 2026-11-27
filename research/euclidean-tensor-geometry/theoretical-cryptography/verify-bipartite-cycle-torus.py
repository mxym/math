#!/usr/bin/env python3
"""Integer small-instance checks for the bipartite Gaussian cycle torus."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial, prod


def falling(n, k):
    return 0 if k > n else factorial(n)//factorial(n-k)


def nega(x):
    return tuple(-u for u in x)


def oriented_cycles(n, m):
    result = {}
    for k in range(2, min(n,m)+1):
        shapes = []
        for rowset in combinations(range(n),k):
            for rowtail in permutations(rowset[1:]):
                rows = rowset[:1]+rowtail
                for cols in permutations(range(m),k):
                    x = [0]*(n*m)
                    for u in range(k):
                        x[rows[u]*m+cols[u]] = 1
                        x[rows[(u+1)%k]*m+cols[u]] = -1
                    shapes.append(tuple(x))
        assert len(set(shapes)) == len(shapes) == falling(n,k)*falling(m,k)//k
        shape_set = set(shapes)
        assert all(nega(x) in shape_set for x in shapes)
        result[k] = shapes
    return result


def energy(x):
    return sum(u*u for u in x)


def finish(y,n,m):
    X = [(list(y[i*(m-1):(i+1)*(m-1)])) for i in range(n-1)]
    for row in X:
        row.append(-sum(row))
    X.append([-sum(row[j] for row in X) for j in range(m)])
    return tuple(u for row in X for u in row)


def decomposition(x, shapes):
    remaining = x
    out = []
    while any(remaining):
        next_cycle = next(c for c in shapes
                          if all(b*a >= int(b != 0) for a,b in zip(remaining,c)))
        out.append(next_cycle)
        remaining = tuple(a-b for a,b in zip(remaining,next_cycle))
    return tuple(out)


def multiset_upper(n,m,max_energy):
    out = [1]+[0]*max_energy
    for k in range(2,min(n,m)+1):
        N = falling(n,k)*falling(m,k)//k
        old = out[:]
        for l in range(1,max_energy//(2*k)+1):
            w = comb(N+l-1,l)
            for y in range(max_energy-2*k*l+1):
                out[y+2*k*l] += w*old[y]
    return out


def vertex_sets(c,n,m):
    edges = [divmod(k,m) for k,x in enumerate(c) if x]
    row, col = (set(r for r,s in edges),set(s for r,s in edges))
    return row,col


def check_disjoint(n,m,cycles):
    labelled = [(k,x,*vertex_sets(x,n,m)) for k,seq in cycles.items() for x in seq]
    pairs = Counter()
    for (h,x,a,b),(k,y,c,d) in combinations(labelled,2):
        if a.isdisjoint(c) and b.isdisjoint(d):
            pairs[h,k] += 1
    for h in cycles:
        for k in cycles:
            if h <= k:
                J = falling(n,h+k)*falling(m,h+k)//(h*k*(2 if h==k else 1))
                assert pairs[h,k] == J
    return sum(pairs.values())


def check_moments(n,m,cycles):
    shapes = [x for xs in cycles.values() for x in xs]
    tests = 0
    zero_triples = 0
    for r in (1,2,3):
        for xs in product(shapes,repeat=r):
            multiplicities = tuple(sum(cx != 0 for cx in col) for col in zip(*xs))
            sums = tuple(map(sum,zip(*xs)))
            vr,vc = map(len,vertex_sets(multiplicities,n,m))
            S = sum(multiplicities)
            e = sum(u != 0 for u in multiplicities)
            s1 = sum(u == 1 for u in multiplicities)
            assert 2*vr <= e and 2*vc <= e and 2*e <= S+s1
            exponent = energy(sums)
            assert exponent >= s1
            if 4*vr == 4*vc == S+s1:
                # In the equality diagrams, a component of double-used edges
                # consists of inverse-cycle pairs unless there is extra q loss.
                if exponent == s1:
                    partition = []
                    for x in xs:
                        absolute = tuple(abs(u) for u in x)
                        if absolute not in partition:
                            partition.append(absolute)
                        else:
                            assert nega(x) in xs
                    test = []
                    for h in partition:
                        a,b = vertex_sets(h,n,m)
                        assert all(a.isdisjoint(c) and b.isdisjoint(d)
                                   for c,d in test)
                        test.append((a,b))
            if r == 3 and all(energy(x) == 4 for x in xs) and exponent == 0:
                zero_triples += 1
            tests += 1
    assert zero_triples == 12*(comb(n,2)*comb(m,3)+comb(n,3)*comb(m,2))
    return tests


def check_grams():
    count = 0
    for p,l in combinations((3,5,7,11),2):
        for a,b in product(range(1-p,p-1),range(1-l,l-1)):
            d = l*a+p*b
            trace = p*l*int(d%(p*l)==0)-p*int(d%p==0)-l*int(d%l==0)+1
            assert trace == (p*int(a==0)-1)*(l*int(b==0)-1)
            count += 1
    return count


def main():
    check_count = sum(check_moments(n,m,oriented_cycles(n,m))
                      for n,m in ((2,2),(2,3),(3,3),(3,4)))
    disjoint = sum(check_disjoint(n,m,oriented_cycles(n,m))
                   for n,m in ((4,4),(4,5),(5,5)))
    tested = 0
    for n,m in ((2,2),(2,3),(3,3),(3,4)):
        cycles = oriented_cycles(n,m)
        shapes = [x for xs in cycles.values() for x in xs]
        coeff = Counter()
        for y in product(range(-3,4),repeat=(n-1)*(m-1)):
            x = finish(y,n,m)
            E = energy(x)
            if E > 12:
                continue
            decomp = decomposition(x,shapes)
            assert sum(energy(c) for c in decomp) == sum(map(abs,x)) <= E
            if decomp:
                assert tuple(map(sum,zip(*decomp))) == x
            coeff[E] += 1
            tested += 1
        assert coeff[0] == 1 and coeff[4] == len(cycles[2])
        assert coeff[6] == len(cycles.get(3,()))
        upper = multiset_upper(n,m,12)
        for h in range(13):
            assert sum(coeff[j] for j in range(h+1)) <= sum(upper[:h+1])
    print(f"PASS: {tested} signed flow decompositions, {disjoint} disjoint "
          f"cycle pairs, {check_count} exact overlap diagrams, and "
          f"{check_grams()} tensor trace Gram entries.")


if __name__ == "__main__":
    main()
