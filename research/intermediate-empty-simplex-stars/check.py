"""Finite exact checks of the overlap ledger and exponent arithmetic only."""
from fractions import Fraction as F
from itertools import combinations, product


def must(condition, message):
    if not condition:
        raise RuntimeError(message)


def exponent(d, k):
    if not isinstance(d, int) or not isinstance(k, int) or not 2 <= k <= d - 1:
        raise ValueError("expected integer 2 <= k <= d-1")
    return d-k + min(F(1), F(k, d-k+2))


def main():
    rows = 0
    for d in range(3, 61):
        for k in range(2, d):
            c, r = d-k+2, d-k+1
            e = exponent(d, k)
            lo = d+1-k + min(0, F(k, c)-1)
            hi = min(r, r-1+F(k, c))
            must(e == lo == hi and e > d-k, (d, k, e))
            must((e == r) == (2*k >= d+2), "saturation threshold")
            rows += 1
    must(exponent(3, 2) == F(5, 3) and exponent(4, 3) == 2, "examples")
    cases = 0
    for r, universe, t in [(2, 6, 3), (2, 5, 4), (3, 6, 3)]:
        choices = tuple(sum(1 << i for i in s) for s in combinations(range(universe), r))
        for sets in product(choices, repeat=t):
            union = 0
            kept = 0
            used = 0
            for s in sets:
                union |= s
                if not used & s:
                    used |= s
                    kept += 1
            v = union.bit_count()
            ell = t*r-v
            target = max(t-ell, 0)
            must(kept >= target, (sets, ell, kept))
            must(v-target <= (r-1)*t, (r,t,v,target))
            cases += 1
    print(f"PASS {rows} rational exponent rows, {cases} exact ordered overlap patterns; no stochastic simulation.")


if __name__ == "__main__":
    main()
