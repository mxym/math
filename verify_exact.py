"""Exact subset dynamic programming and minimizer-partition transitions."""
from functools import cache
from itertools import combinations
from random import Random


def costs_crown(n, denominator, penalty):
    m = n // 2
    a, b = tuple(range(n-m)), tuple(range(n-m, n))
    match = set(zip(a[:n-m-1], b))
    cross = [(1 << i) | (1 << j) for i in a for j in b if (i, j) not in match]
    same = [(1 << i) | (1 << j) for side in (a, b)
            for i, j in combinations(side, 2)]
    return tuple((denominator-penalty)*any(s & e == e for e in cross)
                 + penalty*any(s & e == e for e in same) for s in range(1 << n))


def verify(w, n, thresholds=True):
    """Check optimum, extrema over all greedy ties, and every threshold."""
    full = (1 << n) - 1
    start = tuple(1 << i for i in range(n))
    assert len(w) == full + 1
    assert all(w[s] <= w[s | i] for s in range(full+1) for i in start)

    @cache
    def next_states(parts):
        if len(parts) <= 1:
            return ()
        cand = [(w[a | b], a, b) for a, b in combinations(parts, 2)]
        minimum = min(x[0] for x in cand)
        return tuple((a | b, tuple(sorted(
            [p for p in parts if p not in (a, b)] + [a | b])))
            for c, a, b in cand if c == minimum)

    def solve(score):
        @cache
        def opt(s):
            if not s & (s - 1):
                return 0
            least = s & -s
            a = (s - 1) & s
            lo = float("inf")
            while a:
                if a & least:
                    lo = min(lo, opt(a)+opt(s ^ a))
                a = (a - 1) & s
            return score[s] + lo

        @cache
        def greed(p):
            choices = next_states(p)
            if not choices:
                return (0, 0)
            possible = []
            for s, new in choices:
                follow = next_states(new)
                assert not follow or w[follow[0][0]] >= w[s]
                a, b = greed(new)
                possible.append((score[s]+a, score[s]+b))
            return min(a for a, _ in possible), max(b for _, b in possible)

        return opt(full), *greed(start)

    ans = solve(w)
    opt, lo, hi = ans
    m = n // 2
    assert opt <= lo <= hi and hi-opt <= (m-1)*w[full]
    assert hi <= m*opt
    if thresholds:
        for t in set(w) | {0}:
            base, less, more = solve(tuple(v > t for v in w))
            r, g = base + 1, more + 1
            assert base <= less <= more
            assert g <= (n+r)//2
            if r == 1:
                assert g == 1
            else:
                assert g-r <= (n-r)//2 <= m-1
    return ans


def main():
    fixed = 0
    for n in range(2, 13):
        for den in (2*n, 13*n):
            pen = int(n > 2)
            w = costs_crown(n, den, pen)
            g = (n//2)*den - pen*(n % 2 == 0)
            o = den + (n-2)*pen if n >= 4 else den
            assert verify(w, n) == (o, g, g)
            assert 3*(den+2*g) <= (n//2*2+1)*(den+2*o)
            fixed += 1
    for n in range(2, 9):
        assert verify(costs_crown(n, 1, 0), n) == (1, 1, n//2)
    print(f"PASS exact weighted crown: {fixed} cases through n=12, all ties; "
          "7 deterministic-query extrema")

    monotone_count = []
    for n in range(2, 5):
        leaves = tuple(1 << i for i in range(n))
        subsets = tuple(range(1 << n))
        implications = tuple((s, s | i) for s in subsets for i in leaves if not s & i)
        count = 0
        for code in range(1 << len(subsets)):
            w = tuple(code >> s & 1 for s in subsets)
            if any(w[a] > w[b] for a, b in implications):
                continue
            verify(w, n)
            count += 1
        monotone_count.append(count)
    assert monotone_count == [6, 20, 168]
    print("PASS all Boolean monotone weights: n=2,3,4 counts 6,20,168; "
          "every optimal threshold comparison")

    rng = Random(20261127)
    for trial in range(112):
        n = 3 + trial % 5
        one_dnf = [([rng.randrange(1, 1 << n)
                    for _ in range(rng.randrange(1, 7))], rng.randrange(1, 9))
                   for _ in range(rng.randrange(2, 8))]
        w = tuple(sum(mult for terms, mult in one_dnf if any(s & r == r for r in terms))
                  for s in range(1 << n))
        verify(w, n)
    print("PASS weighted monotone controls: 112 exact instances (n=3..7)")
    # Negative control: a small parent may not have a costlier child
    # in the theorem; removing this assumption invalidates the bound.
    w = tuple(0 if s.bit_count() in (0, 1, 3) else 1 for s in range(8))
    try:
        verify(w, 3)
    except AssertionError:
        print("PASS negative control: reject nonmonotone weight")
    else:
        raise AssertionError("nonmonotone input accepted")


if __name__ == "__main__":
    main()
