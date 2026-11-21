"""Reconstruct the four formal theta pairs exactly through exponent 50."""
from fractions import Fraction as Q
from functools import cache
from itertools import product
from pathlib import Path
import runpy

prior = Path(__file__).resolve().parents[1] / "rank-34-short-support" / "verify.py"
original = runpy.run_path(str(prior))
chi, series = original["chi"], original["series"]
cut = 50
controls = {
    2: (0, 0, 0, 0, 0, 0, 2632, 1000),
    4: (0, 0, 0, 0, 0, 8162, 24612, 92658),
    6: (0, 0, 0, 8632, 2, 0, 173604, 738030),
    8: (0, 0, 0, 61920, 0, 2, 1223700, 5255634),
}


@cache
def form(k, left):
    small = series(k, left)
    return small + [
        sum(d**(k-1)*chi(d if left else n//d) for d in range(1, n+1) if n%d == 0)
        for n in range(len(small), cut+1)]


@cache
def pair(a, left, right):
    f, g = form(a, left), form(22-a, right)
    return [sum(f[i]*g[n-i] for i in range(n+1)) for n in range(cut+1)]


def fourier_basis():
    basis = {}
    for a, left, right in product(range(3, 12, 2), (False, True), (False, True)):
        b = 22-a
        x = list(map(Q, pair(a, left, right)))
        exponent = (2*left-1)*((a-1)//2) + (2*right-1)*((b-1)//2)
        # Minus the Fricke image. Determinant scaling is applied after elimination.
        y = [Q(7)**exponent * v for v in pair(a, not left, not right)]
        for i in range(15):
            if not x[i]:
                continue
            t = x[i]
            if i not in basis:
                basis[i] = ([v/t for v in x], [v/t for v in y])
                break
            px, py = basis[i]
            x = [v-t*u for v, u in zip(x, px)]
            y = [v-t*u for v, u in zip(y, py)]
    assert len(basis) == 15
    return basis


def main():
    basis = fourier_basis()
    for q, prefix in controls.items():
        target = (1,) + (0,)*6 + prefix
        x, y = [Q(0)]*(cut+1), [Q(0)]*(cut+1)
        for i, v in enumerate(target):
            t = v-x[i]
            px, py = basis[i]
            x = [s+t*u for s, u in zip(x, px)]
            y = [s+t*u for s, u in zip(y, py)]
        y = [v*7**(11-q//2) for v in y]
        assert x[:15] == list(target) and x[0] == y[0] == 1
        assert all(v.denominator == 1 and v >= 0 and v%2 == 0 for v in x[1:]+y[1:])
        assert y[1] == 0 and x[7:10] == [0, 0, 0]
        assert y[2] >= 462 and y[3] >= 41058 and y[4] >= 3156588
        if q == 2:
            assert all(x[7*j] == y[j] for j in range(cut//7+1))
        print(44-q, *map(int, y[1:5]))


if __name__ == "__main__":
    main()
