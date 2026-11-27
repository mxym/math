#!/usr/bin/env python3
"""Independent integer incidence and moment checks on weighted point laws."""
from itertools import combinations, product
from random import Random


def area(a, b, c):
    x, y = a
    u, v = b
    s, t = c
    return x*(v-t)+u*(t-y)+s*(y-v)


def rational_best(points):
    best = max(points.values())
    for a, b in combinations(points, 2):
        if a[0] != b[0]:
            best = max(best, sum(w for c, w in points.items() if area(a, b, c) == 0))
    return best


def modular_best(points, p):
    return max(sum(w for (x, y), w in points.items() if (a*x+b-y) % p == 0)
               for a, b in product(range(p), repeat=2))


def log_floor(n, p):
    k = 0
    while n >= p:
        n //= p
        k += 1
    return k


def check_law(points, n, set_of_primes):
    total = sum(points.values())
    a = rational_best(points)
    wt2, wt3 = {}, {}
    for u, v in product(points, repeat=2):
        if u[0] == v[0]:
            d = abs(u[1]-v[1])
            if d:
                wt2[d] = wt2.get(d, 0)+points[u]*points[v]
        else:
            for w in points:
                d = abs(area(u, v, w))
                if d:
                    assert d <= n*n
                    wt3[d] = wt3.get(d, 0)+points[u]*points[v]*points[w]
    event_numerator = sum_gain = sum_loss = 0
    for p in set_of_primes:
        b = modular_best(points, p)
        gain = max(b-a, 0)
        loss = max(a-b, 0)
        pair = sum(w for d, w in wt2.items() if d % p == 0)
        triple = sum(w for d, w in wt3.items() if d % p == 0)
        assert gain**3 <= pair*total+triple
        event_numerator += pair*total+triple
        sum_gain += gain
        sum_loss += loss
    k = len(set_of_primes)
    l1 = log_floor(n, min(set_of_primes))
    l2 = log_floor(n*n, min(set_of_primes))
    assert event_numerator <= (l1+l2)*total**3
    assert sum_gain**3 <= (l1+l2)*k**2*total**3
    assert sum_loss <= l1*total


def main():
    # With x constant, the vertical pair term cannot be dropped.
    same_x = {(0,0):1, (0,2):1}
    assert rational_best(same_x) == 1 and modular_best(same_x,2) == 2
    assert all(area(*t) == 0 for t in product(same_x, repeat=3))
    # Same x-residue but different y-residues can make the modular optimum lower.
    reverse = {(0,0):1, (2,1):1}
    assert rational_best(reverse) == 2 and modular_best(reverse,2) == 1
    # Distinct x and p>n: the three-point event is needed.
    tri = {(0,0):1, (3,1):1, (1,2):1}
    assert rational_best(tri) == 2 and modular_best(tri,5) == 3
    for n, pt, p in ((2,same_x,2),(2,reverse,2),(3,tri,5)):
        check_law(pt,n,(p,))
    print('PASS three separate controls: vertical alias, reverse loss, nonzero determinant')

    rng = Random(574)
    count = 0
    for n in range(1,6):
        grid = tuple(product(range(n+1), repeat=2))
        for i in range(24):
            sizes = min((i % 11)+1, len(grid))
            pts = {z:rng.randrange(1,8) for z in rng.sample(grid, sizes)}
            base_primes = [2,3,5,7,11,13,17,19,23,29]
            chosen = tuple(rng.sample(base_primes, 1+(i % 7)))
            check_law(pts,n,chosen)
            count += 1
    print(f'PASS weighted event and averaged inequalities: {count} exact grid laws')

    trips = 0
    for n in range(1,6):
        grid = tuple(product(range(n+1), repeat=2))
        values = [abs(area(*t)) for t in product(grid, repeat=3)]
        assert max(values) == n*n
        trips += len(values)
    print(f'PASS determinant box bound attained: {trips} ordered triples')


if __name__ == '__main__':
    main()
