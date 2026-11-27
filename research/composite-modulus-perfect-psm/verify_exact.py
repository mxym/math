#!/usr/bin/env python3
"""Check actual GL2 transcript fibres, with no random sampling."""
from collections import Counter
from itertools import product


def mult(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a*e+b*g) % p, (a*f+b*h) % p,
            (c*e+d*g) % p, (c*f+d*h) % p)


def row(x, y, p):
    a, b = x
    c, d, e, f = y
    return ((a*c+b*e) % p, (a*d+b*f) % p)


def col(x, y, p):
    a, b, c, d = x
    e, f = y
    return ((a*e+b*f) % p, (c*e+d*f) % p)


def dot(r, c, p):
    return (r[0]*c[0] + r[1]*c[1]) % p


def inverse(x, p):
    a, b, c, d = x
    t = pow((a*d-b*c) % p, -1, p)
    return tuple(z*t % p for z in (d, -b, -c, a))


def gl2(p):
    group = tuple(x for x in product(range(p), repeat=4)
                  if (x[0]*x[3]-x[1]*x[2]) % p)
    assert len(group) == (p*p-1)*(p*p-p)
    return group


def params(p, q):
    assert (p-1) % q == 0
    return next(g for g in range(1, p) if pow(g, q, p) == 1
                and all(pow(g, j, p) != 1 for j in range(1, q)))


def expected(p, output):
    vectors = [x for x in product(range(p), repeat=2) if any(x)]
    return {(r, c): (p-1) * (p if output else 1)
            for r in vectors for c in vectors if (dot(r, c, p) == 0) == output}


def check_all():
    trials = 0
    for p, q, n in ((3, 2, 2), (3, 2, 3), (5, 4, 2), (7, 6, 2)):
        group = gl2(p)
        inv = {a: inverse(a, p) for a in group}
        g = params(p, q)
        D = ((1, 0, 0, 1), (g, 0, 0, 1))
        for x in product((0, 1), repeat=n):
            output = sum(x) % q == 0
            hist = {}
            expect = expected(p, output)
            for gs in product(group, repeat=n-1):
                m = tuple(mult(mult(inv[gs[i-1]], D[x[i]], p), gs[i], p)
                          for i in range(1, n-1))
                a = row((g if x[0] else 1, p-1), gs[0], p)
                c = col(inv[gs[-1]], (g if x[-1] else 1, 1), p)
                B = (1, 0, 0, 1)
                for mat in m:
                    B = mult(B, mat, p)
                h = hist.setdefault(m, Counter())
                for s in range(1, p):
                    cs = tuple(t*s % p for t in c)
                    cp = col(B, cs, p)
                    assert dot(a, cp, p) == ((pow(g, sum(x), p)-1)*s) % p
                    h[a, cp] += 1
                    trials += 1
            assert len(hist) == len(group)**(n-2)
            assert all(h == expect for h in hist.values())
    return trials


def check_conditioned():
    # Include distinct positive accepting weights, composite q, and nonidentity,
    # noncommuting middle messages. Test raw endpoint law after exact seed inversion.
    trials = fibres = 0
    for p, q, n in ((5, 4, 6), (7, 6, 7)):
        group = gl2(p)
        inv = {a: inverse(a, p) for a in group}
        g = params(p, q)
        D = ((1, 0, 0, 1), (g, 0, 0, 1))
        negD = (D[0], inv[D[1]])
        base = [(0,)*n] + [(1,)*w+(0,)*(n-w) for w in range(1, n+1)]
        for middle in (tuple(group[(i*369+4) % len(group)] for i in range(n-2)),
                       ((1, 0, 0, 1),)*(n-2)):
            B = (1, 0, 0, 1)
            for mat in middle:
                B = mult(B, mat, p)
            for x in base + [y[1:] + y[:1] for y in base[1:-1]]:
                output = sum(x) % q == 0
                h = Counter()
                for first in group:
                    last = first
                    for bit, target in zip(x[1:-1], middle):
                        prev = last
                        last = mult(mult(negD[bit], prev, p), target, p)
                        assert mult(mult(inv[prev], D[bit], p), last, p) == target
                    a = row((g if x[0] else 1, p-1), first, p)
                    c = col(inv[last], (g if x[-1] else 1, 1), p)
                    for s in range(1, p):
                        cp = col(B, tuple(t*s % p for t in c), p)
                        assert (dot(a, cp, p) == 0) == output
                        h[a, cp] += 1
                        trials += 1
                assert h == expected(p, output)
                fibres += 1
    return trials, fibres


def check_group_sizes_and_controls():
    checks = 0
    for p in (2, 3, 5, 7):
        group = gl2(p)
        iv = {a: inverse(a, p) for a in group}
        for t in range(p):
            a = (t, int(t == 0))
            b = (1, 0)
            hist = Counter((row(a, A, p), col(iv[A], b, p)) for A in group)
            size = (p*p-1)*(p if t else p-1)
            assert len(hist) == size
            assert set(hist.values()) == {len(group)//size}
            assert all(dot(r, c, p) == t and any(r) and any(c) for r, c in hist)
            checks += 1
    # Diagnostic only: retaining actual vectors but deleting the required
    # scalar mask breaks the specified equal-law property in this toy model.
    p, q = 5, 4
    g = params(p, q)
    assert ((g-1) % p) != ((g*g-1) % p) and (g-1) % p and (g*g-1) % p
    # Fixed arithmetic quotient gives correct function for all small q>n too.
    cut = 0
    for n in range(1, 40):
        for q in range(2, 60):
            m = min(q, n+1)
            for w in range(n+1):
                assert (w % q == 0) == (w % m == 0)
                cut += 1
    return checks, cut


if __name__ == "__main__":
    full = check_all()
    partial, conditions = check_conditioned()
    orbits, cut = check_group_sizes_and_controls()
    print(f"PASS exact: {full} full seeds; {partial} conditioned seeds in {conditions} fibres")
    print(f"PASS exact: {orbits} GL2 contraction orbits; {cut} cutoff cases; scalar-mask control")
