"""Exhaustive finite additive cube counts and exact prime-field Fourier checks."""
from collections import Counter
from itertools import product


def add(x, y, p):
    return tuple((a+b) % p for a, b in zip(x, y))


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def add_subsets(directions, d, p):
    points = ((0,)*d,)
    for h in directions:
        points = points + tuple(add(u, h, p) for u in points)
    return points


def independent(hs, d, p):
    span = {(0,)*d}
    for h in hs:
        if h in span:
            return False
        span = {add(u, tuple(a*x % p for x in h), p)
                for u in span for a in range(p)}
    return True


def finite_census(p, d, q, z):
    grid = tuple(product(range(p), repeat=d))
    N = len(grid)
    lookup = {x: i for i, x in enumerate(grid)}
    assert pow(z, p, q) == 1 and z != 1 and N % q
    Fourier_cubes = 0
    for s in range(d+1):
        all_shapes, admissible = Counter(), Counter()
        directions_total = 0
        for hs in product(grid, repeat=s):
            off = add_subsets(hs, d, p)
            ind = independent(hs, d, p)
            directions_total += ind
            if ind:
                assert len(set(off)) == 2**s
            for x in grid:
                vertices = tuple(add(x, h, p) for h in off)
                mask = 0
                for v in vertices:
                    mask |= 1 << lookup[v]
                all_shapes[mask] += 1
                if not ind:
                    continue
                admissible[mask] += 1
                spectrum = {v: (-1)**j.bit_count() for j, v in enumerate(vertices)}
                inverse_values = []
                for y in grid:
                    direct = sum(a*pow(z, -dot(v, y) % p, q)
                                 for v, a in spectrum.items()) % q
                    factored = pow(z, -dot(x, y) % p, q)
                    for h in hs:
                        factored *= 1-pow(z, -dot(h, y) % p, q)
                    assert direct == factored % q
                    value = (direct * pow(N, -1, q)) % q
                    assert bool(value) == all(dot(h, y) % p != 0 for h in hs)
                    inverse_values.append(value)
                v = (1, 0, 2)
                word_weight = sum(bool(t*a % q) for t in v for a in inverse_values)
                assert word_weight == 2*(p-1)**s*p**(d-s)
                Fourier_cubes += 1

        exact_independent = 1
        for i in range(s):
            exact_independent *= N-p**i
        assert directions_total == exact_independent
        assert sum(all_shapes.values()) == N**(s+1)
        assert sum(admissible.values()) == N*exact_independent

        for S in range(1 << N):
            tot = sum(n for a, n in all_shapes.items() if S & a == a)
            gd = sum(n for a, n in admissible.items() if S & a == a)
            assert tot * N**(2**s) >= S.bit_count()**(2**s) * N**(s+1)
            # alpha**(2**s) >= p**(s-d) without floating point.
            if S.bit_count()**(2**s) * p**(d-s) >= N**(2**s):
                assert gd
    return Fourier_cubes, (1 << N)*(d+1)


def negative_sign_control():
    grid = tuple(product(range(3), repeat=2))
    z, q = 2, 7
    good = tuple((1-pow(z, -x[0] % 3, q)) % q for x in grid)
    bad = tuple((1+pow(z, -x[0] % 3, q)) % q for x in grid)
    assert sum(map(bool, good)) == 6
    assert sum(map(bool, bad)) == 9


if __name__ == "__main__":
    a = finite_census(2, 3, 3, 2)
    b = finite_census(3, 2, 7, 2)
    assert a == (1744, 1024) and b == (513, 1536)
    print(f"PASS exhaustive cube counting: {a[1]+b[1]} subset/dimension pairs; "
          f"{a[0]+b[0]} independent affine cubes and exact inverse supports")
    negative_sign_control()
    print("PASS signed-spectrum negative control: flipped sign changes support 6 -> 9")
