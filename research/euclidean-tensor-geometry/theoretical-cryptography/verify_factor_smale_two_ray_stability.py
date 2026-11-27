"""Exact algebraic fixtures for FactorSmaleTwoRayStability.md."""
from fractions import Fraction as F
from random import Random

Z = (F(0), F(0))
ONE = (F(1), F(0))
NEG = (F(-1), F(0))
K = F(2, 3)
checks = 0


def check(condition):
    global checks
    assert condition
    checks += 1


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def scale(x, k):
    return x[0]*k, x[1]*k


def mul(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def norm2(x):
    return x[0]**2+x[1]**2


def integral(roots, endpoint):
    """Product of (1 - t*endpoint/root), then exact integration."""
    coefs = [ONE]
    for q in roots:
        v = scale(mul(endpoint, (q[0], -q[1])), -1/norm2(q))
        arr = coefs + [Z]
        for j, c in enumerate(coefs, 1):
            arr[j] = add(arr[j], mul(c, v))
        coefs = arr
    return tuple(sum(c[i]/(j+1) for j, c in enumerate(coefs))
                 for i in range(2))


def unit(t):
    d = 1+t*t
    return (t*t-1)/d, 2*t/d


def verify_bound(u, first, second, angle):
    first, second = list(first), list(second)
    roots = [(F(1), F(0)), scale(angle, u)]
    roots += [(k, F(0)) for k in first]
    roots += [scale(angle, k) for k in second]
    a = sum(1/x for x in second) - sum(1/x for x in first)
    b = K*(1-1/u)
    e = sum(1/x**2 for x in first+second)
    d = 1+angle[0]
    lam = F(5, 3024)
    if u <= 2:
        v = abs(a-b)/8 + F(e, 288) + d/36
        gap = lam*(u-1)**2+F(5,128)*min(1, v)
    else:
        gap = lam
    chosen = roots[0 if a <= b else 1]
    check(norm2(integral(roots, chosen)) <= (K-gap)**2)
    # The exact angular factor identity, before exponential majorization.
    s = 1/u if a <= b else u
    x = s/7
    ratio = norm2(add(ONE, scale(angle, -x)))/(1+x)**2
    check(ratio == 1 - 2*x*d/(1+x)**2)


def run():
    rng = Random(879431)
    for _ in range(410):
        u = rng.choice((F(1), F(2), F(rng.randrange(1, 47), 23)+1,
                        1+F(rng.randrange(1, 100), 10000)))
        angle = unit(F(rng.randrange(-30, 31), 23))
        first = [F(rng.randrange(17,100), 17) for _ in range(rng.randrange(7))]
        second = [u*F(rng.randrange(17,100),17) for _ in range(rng.randrange(7))]
        verify_bound(u, first, second, angle)
    for n in range(10, 91):
        h = F(1,n)
        r = 1/(1+h)
        b = K*(1-r)
        points = [ONE, (-1/r, F(0)), (-1/b, F(0))]
        expected = [K-(r-1)**2/18, K-h*h/18, F(3,4)-r/(12*b*b)]
        for c, t in zip(points, expected):
            check(integral(points, c) == (t, F(0)))
        check(min(map(abs,expected)) == K-h*h/18)
        chk2 = (r-1+b)/2
        check(chk2 == (r-1)/6)
        verify_bound(1+h, [], [1/b], NEG)
    for n in range(4,90):
        m = F(n)
        points = [ONE, NEG, (m, F(0)), (-m, F(0))]
        for c in points[:2]:
            check(integral(points, c) == (K-F(2,15)/m**2, F(0)))
        for c in points[2:]:
            check(integral(points, c) == (K-F(2,15)*m**2, F(0)))
        points.pop()
        check(integral(points, ONE) == (K-1/(4*m), F(0)))
        check(integral(points, NEG) == (K+1/(4*m), F(0)))
        check(integral(points, points[-1]) == (F(1,2)-m*m/12, F(0)))
        a = unit(1/m)
        points = [ONE, a]
        for c in points:
            check(norm2(integral(points, c)) == F(4,9)-(1+a[0])/6)
    print(f"Two-ray stability fixtures passed: {checks} exact assertions.")


if __name__ == "__main__":
    run()
