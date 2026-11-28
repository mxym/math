#!/usr/bin/env python3
"""Exact small-case replay; schoolbook polynomial arithmetic is intentional."""
from itertools import combinations
from math import gcd, isqrt, lcm, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def power_two_exponent(n):
    return (n & -n).bit_length() - 1


def carmichael(factors):
    exponents = []
    for p, a in factors:
        exponents.append(2 ** (a - 2) if p == 2 and a >= 3
                         else p ** (a - 1) * (p - 1))
    return lcm(*exponents)


def ceil_sqrt(n):
    q = isqrt(n)
    return q + (q * q != n)


def first_true(lo, hi, pred):
    while lo <= hi:
        mid = (lo + hi) // 2
        if pred(mid):
            hi = mid - 1
        else:
            lo = mid + 1
    return lo


def icbrt(n):
    return first_true(0, 1 << ((n.bit_length() + 2) // 3),
                      lambda s: s**3 > n) - 1


def mul(f, g, n):
    h = [0] * (len(f) + len(g) - 1)
    for i, fi in enumerate(f):
        for j, gj in enumerate(g):
            h[i + j] = (h[i + j] + fi * gj) % n
    return h


def tree(fs, n):
    if len(fs) == 1:
        return fs[0], None, None
    k = len(fs) // 2
    a, b = tree(fs[:k], n), tree(fs[k:], n)
    return mul(a[0], b[0], n), a, b


def rem(f, g, n):
    assert g[-1] == 1
    r = f[:]
    while len(r) >= len(g):
        top = r.pop()
        k = len(r) - len(g) + 1
        for i, gi in enumerate(g[:-1]):
            r[k + i] = (r[k + i] - top * gi) % n
    return r


def evaluations(f, query_tree, n):
    r = rem(f, query_tree[0], n)
    a, b = query_tree[1:]
    if a is None:
        return r
    return evaluations(r, a, n) + evaluations(r, b, n)


def progression(n, g, lo, hi, marks):
    if lo > hi:
        return None
    count = hi - lo + 1
    width = ceil_sqrt(count)
    blocks, tail = divmod(count, width)
    f, _, _ = tree([[(1 + g * (lo + j)) % n, g * width % n]
                    for j in range(width)], n)
    values = evaluations(f, tree([[(-k) % n, 1] for k in range(blocks)], n), n)
    assert values == [prod(1 + g * (lo + k * width + j)
                           for j in range(width)) % n for k in range(blocks)]
    marks["multiblock"] |= blocks > 1
    for k, value in enumerate(values):
        d = gcd(n, value)
        if 1 < d < n:
            return d
        if d == n:
            marks["full"] = True
            for j in range(lo + k * width, lo + (k + 1) * width):
                d = gcd(n, 1 + g * j)
                if 1 < d < n:
                    return d
            raise AssertionError("full block had no proper leaf")
    for j in range(lo + blocks * width, lo + blocks * width + tail):
        d = gcd(n, 1 + g * j)
        if 1 < d < n:
            marks["tail"] = True
            return d
    return None


def cubic_roots(s, w, ell):
    """All distinct positive integer roots up to ell, with monotone segments."""
    p = lambda x: ((x - s) * x + w) * x - ell
    diff = lambda x: 3 * x * x + (3 - 2 * s) * x + (1 - s + w)
    if ell == 1:
        return (1,) if p(1) == 0 else ()
    vertex = max(1, min(ell - 1, -((3 - s) // 3)))
    if diff(vertex) >= 0:
        segments = [(1, ell, 1)]
    else:
        left = first_true(1, vertex, lambda x: diff(x) < 0)
        right = first_true(vertex, ell - 1, lambda x: diff(x) >= 0)
        segments = [(1, left, 1), (left, right, -1), (right, ell, 1)]
    roots = set()
    for lo, hi, sign in segments:
        start = first_true(lo, hi, lambda x: sign * p(x) >= 0)
        stop = first_true(start, hi, lambda x: sign * p(x) > 0)
        roots.update(range(start, stop))
    return tuple(sorted(roots))


def squarefree(r, lam, method, marks):
    if (r - 1) % lam:
        return None
    ratio = (r - 1) // lam
    if ratio <= 1:
        return None
    g = isqrt(ratio - 1)
    j = ratio - g * g
    if g < 2 or not (1 <= j <= 2 * g) or lam % g:
        return None
    ell = lam // g
    e = ell * j
    lo = g // j + 1
    hi = min((9 * g - 1) // (2 * j), (icbrt(r) - 1) // g)
    first, last = e % g or g, (3 * ell * j * j - 1) // (g * g)
    if method == "threshold":
        method = "progression" if g**13 <= j**13 * r**2 else "cubic"
    if method == "smaller":
        method = ("progression" if ceil_sqrt(max(0, hi - lo + 1))
                  <= max(0, (last - first) // g + 1) else "cubic")
    marks[method] += 1
    if method == "progression":
        d = progression(r, g, lo, hi, marks)
        if d is None:
            return None
        p = d if prime(d) else r // d
        qr, phi, u = r // p, g * g * lam, p - 1
        if phi % u:
            return None
        total = qr + 1 - phi // u
        disc = total * total - 4 * qr
        if disc < 0:
            return None
        root = isqrt(disc)
        if root * root != disc or (total - root) % 2:
            return None
        candidates = [(p, (total - root) // 2, (total + root) // 2)]
    else:
        candidates = []
        for s in range(first, last + 1, g):
            w = (e - s) // g
            if w <= 0:
                continue
            abc = cubic_roots(s, w, ell)
            if len(abc) == 3 and prod(abc) == ell:
                candidates.append(tuple(1 + g * a for a in abc))
    for ps in candidates:
        if (len(set(ps)) == 3 and prod(ps) == r and all(map(prime, ps))
                and lcm(*(p - 1 for p in ps)) == lam):
            return tuple(sorted(ps))
    return None


def powered(n, lam, method, marks):
    e = power_two_exponent(n)
    odd = n >> e
    z = power_two_exponent(lam)
    candidates = [lam] if e == 0 else [(lam >> z) << j for j in range(z + 1)]
    for exponent in candidates:
        d = gcd(odd, exponent)
        ps = squarefree(odd // d, exponent // d, method, marks)
        if ps is None:
            continue
        actual = [(2, e)] if e else []
        rest = odd
        for p in ps:
            v = 0
            while rest % p == 0:
                v += 1
                rest //= p
            actual.append((p, v))
        if rest == 1 and all(v > 0 for _, v in actual) and carmichael(actual) == lam:
            return tuple(actual)
    return None


def main():
    marks = {"progression": 0, "cubic": 0, "multiblock": False,
             "full": False, "tail": False}
    assert progression(3 * 5 * 7, 2, 1, 5, marks) == 3
    assert progression(101 * 103 * 107, 2, 46, 50, marks) == 101
    assert progression(101 * 103 * 107, 2, 45, 56, marks) == 101 * 103
    assert progression(101 * 103 * 107, 2, 30, 41, marks) is None
    assert all(marks[k] for k in ("multiblock", "full", "tail"))
    checks = 0
    # Compare the three monotone segments to complete bounded enumeration,
    # including repeated roots, stationary steps, endpoints and no root.
    for s in range(1, 28):
        for w in range(1, 90):
            for ell in range(1, 31):
                target = tuple(x for x in range(1, ell + 1)
                               if x**3 - s*x*x + w*x - ell == 0)
                assert cubic_roots(s, w, ell) == target
                checks += 1
    assert cubic_roots(9, 26, 24) == (2, 3, 4)
    assert cubic_roots(7, 16, 12) == (2, 3)  # (x-2)^2 (x-3)
    assert cubic_roots(3, 3, 1) == (1,)
    assert cubic_roots(1, 1, 2) == ()
    examples = set()
    for ps in combinations([2 * i + 1 for i in range(1, 95)
                             if prime(2 * i + 1)], 3):
        r = prod(ps)
        if all((r - 1) % (p - 1) == 0 for p in ps):
            examples.add(ps)
    extras = [(7, 23, 41), (41, 61, 101), (61, 271, 571),
              (103, 647, 1361), (281, 617, 673), (281, 421, 701)]
    examples.update(extras)
    count = 0
    non_simple = 0
    strict_masking = 0
    used = {"progression": 0, "cubic": 0}
    for ps in sorted(examples):
        r, lam = prod(ps), lcm(*(p - 1 for p in ps))
        g = gcd(*(p - 1 for p in ps))
        non_simple += ps[0] != 1 + g
        for method in ("progression", "cubic", "threshold", "smaller"):
            saved = {k: marks[k] for k in used}
            assert squarefree(r, lam, method, marks) == ps
            if method == "smaller":
                for k in used:
                    used[k] += marks[k] - saved[k]
        for a, b, c in [(1, 3, 2), (4, 1, 5), (3, 3, 3)]:
            odd = list(zip(ps, (a, b, c)))
            for e in (0, 1, 2, 4, 13):
                case = ([(2, e)] if e else []) + odd
                n, value = prod(p**v for p, v in case), carmichael(case)
                assert powered(n, value, "smaller", marks) == tuple(case)
                if e and power_two_exponent(value) > power_two_exponent(carmichael(odd)):
                    strict_masking += 1
                count += 1
    assert all(used.values()) and non_simple and strict_masking
    assert squarefree(105, 12, "smaller", marks) is None
    print("progression: multiblock, full-block gcd, tail hit, and no hit")
    print("cubic roots versus complete evaluation:", checks)
    print("C3 radicals / non-simple:", len(examples), non_simple)
    print("count-based branch selections: progression / cubic:",
          used["progression"], used["cubic"])
    print("powered inputs / strict even masking:", count, strict_masking)
    print("PASS")


if __name__ == "__main__":
    main()
