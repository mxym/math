#!/usr/bin/env python3
"""Exact checks for the fixed words and odd-order sharpness examples."""
from itertools import combinations
from math import gcd

ONE = (0, 0, 0)
X, Y = (1, 0, 0), (0, 1, 0)
LABELS = (ONE, X, Y)


def need(test, message):
    if not test:
        raise AssertionError(message)


def mul(s, t):
    a, b, c = s
    u, v, w = t
    return a + u, b + v, c + w - b * u


def inv(s):
    a, b, c = s
    return -a, -b, -c - a * b


def prefixes(steps):
    p = [ONE]
    for s in steps:
        p.append(mul(p[-1], s))
    return p


def differences(paths):
    result = set()
    for path in paths:
        for s, t in combinations(path, 2):
            h = mul(inv(s), t)
            result.add(min(h, inv(h)))
    return result


def exceptional(paths):
    return {
        (a, b, c) for a, b, c in differences(paths)
        if gcd(a, b) != 1 and (a, b, abs(c)) != (0, 0, 1)
    }


def lift_word(w):
    return prefixes(
        (inv(LABELS[a]) if i % 2 else LABELS[a])
        for i, a in enumerate(w)
    )


def words(n):
    """Rooted words of a three-edge bipartite dipole, initial layer fixed."""
    def rec(w):
        if len(w) == n:
            if w[0] != w[-1]:
                yield w
        else:
            for a in range(3):
                if not w or w[-1] != a:
                    yield from rec(w + (a,))
    yield from rec(())


def verify_words():
    pure = prefixes([X, Y, inv(X), Y, X, inv(Y), inv(X), inv(Y)])
    need(pure[-1] == ONE, "ordinary word did not close")
    need(pure[:-1] == [
        (0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 1),
        (0, 2, 1), (1, 2, -1), (1, 1, -1), (0, 1, 0),
    ], "ordinary prefix table")
    need(exceptional([pure[:-1]]) == {(0, -2, -1), (0, -2, 1)},
         "ordinary exceptional differences")
    mixed = prefixes([X, inv(Y), inv(X), inv(Y)])
    need(mixed[-1] == (0, -2, -1), "mixed alternate total")
    need(mixed[:-1] == [ONE, X, (1, -1, 0), (0, -1, -1)],
         "mixed alternate prefix table")

    for s, r, es in (
        ("0101201210102102", ONE,
         {(-3, 0, -2), (-3, 0, 1), (-2, 0, -2), (-2, 0, 0), (-2, 0, 1)}),
        ("01012102", (-3, 0, 1), {(-2, 0, 0)}),
    ):
        need(s[0] == "0" and all(a != b for a, b in zip(s, s[1:] + s[0])),
             "prescribed edge used and no cyclic backtrack")
        p = lift_word(map(int, s))
        need(p[-1] == r, "three-matching total")
        need(exceptional([p[:-1:2], p[1:-1:2]]) == es,
             "three-matching exceptional differences")

    for n, count in ((4, 18), (8, 258)):
        seen = 0
        for w in words(n):
            seen += 1
            a, b, _ = lift_word(w)[-1]
            need(a % 5 or b % 5, "unexpected closed word in the rank-two example")
        need(seen == count, "rank-two base word count")


EDGES = ((1, 4), (1, 5), (2, 4), (2, 5))
PAIRS = tuple(combinations(range(4), 2))
ADJ = {i: tuple(range(3, 6)) if i < 3 else tuple(range(3)) for i in range(6)}


def closed_base_words(n):
    def dfs(vs):
        if len(vs) == n:
            if vs[0] not in ADJ[vs[-1]]:
                return
            if vs[0] != vs[-2] and vs[-1] != vs[1]:
                yield vs
            return
        for q in ADJ[vs[-1]]:
            if len(vs) == 1 or q != vs[-2]:
                yield from dfs(vs + (q,))
    for root in range(3):
        yield from dfs((root,))


def voltage(vs):
    u, c = [0] * 4, [0] * 6
    for h, k in zip(vs, vs[1:] + vs[:1]):
        edge = min(h, k), max(h, k)
        if edge not in EDGES:
            continue
        ind = EDGES.index(edge)
        sign = 1 if h < k else -1
        for ell, (i, j) in enumerate(PAIRS):
            if i == ind:
                c[ell] -= sign * u[j]
        u[ind] += sign
    return u + c


def verify_k33():
    for n, count in ((4, 36), (8, 324), (16, 66564)):
        seen = 0
        for vs in closed_base_words(n):
            seen += 1
            need(any(t % 3 for t in voltage(vs)),
                 "unexpected closed word in the rank-four example")
        need(seen == count, "rank-four base word count")


if __name__ == "__main__":
    verify_words()
    verify_k33()
    print("PASS: fixed-word difference tables and both odd-order sharpness examples")
