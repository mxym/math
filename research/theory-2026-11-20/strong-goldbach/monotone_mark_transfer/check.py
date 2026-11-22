#!/usr/bin/env python3
"""Rational controls for the literal signed divisor transfer (not analytic)."""
from fractions import Fraction as Q

BETA = Q(1, 10)
DELTA = Q(7, 100)
EPS = Q(1, 100)


def check(cond, *args):
    if not cond:
        raise SystemExit(f"FAIL: {args!r}")


def ramp(u, a, b):
    return max(Q(0), min(Q(1), (u - a) / (b - a)))


def phi0(u):
    return 2 * u * ramp(u, BETA, 2 * BETA)


def phi(u):
    return phi0(u) * (1 - ramp(u, Q(1, 2) - DELTA, Q(1, 2) - DELTA / 2))


def g(u):
    return 1 - ramp(u, Q(1, 2) - 2 * EPS, Q(1, 2) - EPS)


def rows(rem, k, smallest=1, top=()):
    if k == 1:
        if rem >= smallest:
            yield top + (rem,)
        return
    for j in range(smallest, rem // k + 1):
        yield from rows(rem - j, k - 1, j + 1, top + (j,))


def scores(us):
    n = len(us)
    T = sum(us)
    h = T / 2
    a0 = Q(0)
    z = zr = zi = f = Q(0)
    for sub in range(1 << n):
        members = [u for i, u in enumerate(us) if sub & (1 << i)]
        a = sum(members, a0)
        if a == h:
            return None  # impossible for a genuine squarefree integer
        s = (-1) ** len(members)
        f += s * abs(a - h)
        z -= s * g(a) * sum(map(phi, members), a0)
        if a < h:
            zr -= s * sum(map(phi, members), a0)
            zi -= s * sum(map(phi0, members), a0)
    return f, z, zr, zi


def mark_factor(us, i):
    u = us[i]
    rest = list(us[:i]) + list(us[i + 1 :])
    acc = Q(0)
    for sub in range(1 << len(rest)):
        members = [v for j, v in enumerate(rest) if sub & (1 << j)]
        acc += (-1) ** len(members) * g(u + sum(members))
    return phi(u) * acc


def run():
    counts = {r: 0 for r in range(1, 5)}
    fringe = {"nongiant_star": 0, "nongiant_triangle": 0, "giant4": 0}
    for total, den in [(73, 73), (89, 89), (97, 96)]:
        for r in range(1, 5):
            for seq in rows(total, r):
                us = tuple(Q(u, den) for u in seq)
                sc = scores(us)
                if sc is None:
                    continue
                f, z, zr, zi = sc
                t = sum(us)
                h = t / 2
                counts[r] += 1
                if r == 1:
                    check(f == z == 0, "rank1", us, sc)
                elif r == 2:
                    check(f == 2 * us[0] and z == phi(us[0]), "rank2", us, sc)
                    if 2 * BETA <= us[0] <= Q(1, 2) - DELTA:
                        check(f == z, "paid rank2", us, sc)
                elif r == 3:
                    check(f == 0 and z >= 0, "rank3", us, sc)
                elif us[-1] < h:
                    a, b, c, d = us
                    if a + d < h:
                        name = "nongiant_star"
                        check(f == -4 * a and zr == -2 * phi(a), name, us, sc)
                    else:
                        name = "nongiant_triangle"
                        check(f == 4 * d - 2 * t and zr == phi(d) - phi(a) - phi(b) - phi(c), name, us, sc)
                    check(z >= zr and f <= zi, "monotone comparison", us, sc)
                    if f > z:
                        check(name == "nongiant_triangle" and d > Q(1, 2) - DELTA
                              and c >= BETA and 0 < h - d < a, "fringe necessity", us, sc)
                        fringe[name] += 1
                else:
                    check(f == 0 and zr == 0, "giant rank4", us, sc)
                    terms = [mark_factor(us, i) for i in range(r)]
                    check(sum(terms) == z, "literal true marks", us, sc, terms)
                    for i, term in enumerate(terms):
                        if term:
                            check(i != r - 1 and Q(1, 2) - 2 * EPS < t - us[-1] < h,
                                  "giant strip", i, us, sc)
                    if f > z:
                        fringe["giant4"] += 1
    adverse = tuple(Q(u, 100) for u in (18, 19, 20, 21, 22))
    # The main illustration uses a lower mark starting at beta'=0.17 or below;
    # for the controls take comparable distinct sizes above 2*beta via a
    # separate fully open low-side weight at the same strict half cut.
    def full_mark_score(us):
        s = Q(0)
        for sub in range(1 << len(us)):
            members = [u for i, u in enumerate(us) if sub & (1 << i)]
            a = sum(members)
            s -= (-1) ** len(members) * g(a) * 2 * a
        return s
    check(scores(adverse)[0] == 0 and full_mark_score(adverse) == -6,
          "rank 5 must not be discarded")
    check(fringe["nongiant_triangle"] > 0 and fringe["giant4"] > 0, "fringe fixtures covered", fringe)
    print("PASS ranks", counts, "| true-fringe patterns", fringe, "| adverse rank-five score 6")

if __name__ == "__main__":
    run()
