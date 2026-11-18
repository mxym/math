"""Check the four possible projective types of a mod-5 left nullvector."""
from itertools import combinations, product


def normal_type(s):
    counts = [sum(abs(v) == k for v in s) for k in (1, 2)]
    # Multiplication by 2 modulo 5 interchanges the two absolute values.
    return tuple(sorted(counts, reverse=True))


def moments(s):
    totals = {(0, 0)}
    for i, j in combinations(range(6), 2):
        for sign in (1, -1):
            b = s[i] + sign * s[j]
            outside = [s[h] for h in range(6) if h not in (i, j)]
            choices = set()
            for entries in product((-2, 2), repeat=4):
                a = b + sum(x * v for x, v in zip(entries, outside))
                if a % 5 == 0:
                    k = a // 5
                    choices.add((k*k, b*k))
            totals = {(x + u, y + v) for x, y in totals for u, v in choices}
    return totals


def verify():
    types = {normal_type(s) for s in product(range(-2, 3), repeat=6)
             if any(s) and sum(a*a for a in s) % 5 == 0}
    assert types == {(1, 1), (2, 2), (3, 3), (5, 0)}
    for a, b in sorted(types):
        s = [1]*a + [2]*b + [0]*(6-a-b)
        norm = sum(x*x for x in s)
        target = (90*norm//25, 2*norm)
        totals = moments(s)
        assert target not in totals
        print((a, b), 'requires', target, 'attainable second moments at first target',
              sorted(y for x, y in totals if x == target[0]))


if __name__ == '__main__':
    verify()
