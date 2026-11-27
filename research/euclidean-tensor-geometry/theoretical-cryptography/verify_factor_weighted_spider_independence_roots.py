"""Exact fixtures for FactorWeightedSpiderIndependenceRoots.md."""
from fractions import Fraction as F
from math import gcd, lcm
from random import Random

checks = 0


def check(ok):
    global checks
    assert ok
    checks += 1


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def add(p, q):
    out = [0]*max(len(p), len(q))
    for j, a in enumerate(p):
        out[j] += a
    for j, b in enumerate(q):
        out[j] += b
    return trim(out)


def mul(p, q):
    out = [0]*(len(p)+len(q)-1)
    for j, a in enumerate(p):
        for i, b in enumerate(q):
            out[i+j] += a*b
    return trim(out)


def path(ws):
    a = b = [1]
    for w in ws:
        a, b = add(a, [0]+[w*t for t in b]), a
    return a


def spider(tau, lists):
    a, b = [1], [1]
    for p in lists:
        a = mul(a, path(p))
        b = mul(b, path(p[1:]))
    return add(a, [0]+[tau*v for v in b])


def brute(tau, legs):
    weights, edges = [tau], []
    for leg in legs:
        u = 0
        for weight in leg:
            v = len(weights)
            edges.append((1 << u) | (1 << v))
            weights.append(weight)
            u = v
    p = [0]*(len(weights)+1)
    for mask in range(1 << len(weights)):
        if any(mask & edge == edge for edge in edges):
            continue
        w = 1
        for i, a in enumerate(weights):
            if (mask >> i) & 1:
                w *= a
        p[mask.bit_count()] += w
    return trim(p)


def neg_primitive_remainder(q, p):
    q = list(map(F, q))
    while q and len(q) >= len(p):
        n = len(q)-len(p)
        c = q[-1]/p[-1]
        for j, x in enumerate(p):
            q[n+j] -= c*x
        trim(q)
    if not q:
        return q
    d = lcm(*(x.denominator for x in q))
    z = [-int(d*x) for x in q]
    g = gcd(*z)
    return [x//g for x in z]


def variations(xs):
    xs = [x for x in xs if x]
    return sum((u > 0) != (v > 0) for u,v in zip(xs, xs[1:]))


def count_negative(p):
    """Sturm's theorem for the interval (-infinity,0)."""
    a = p[:]
    b = [j*a[j] for j in range(1,len(a))]
    seq = [a]
    while b:
        seq.append(b)
        a, b = b, neg_primitive_remainder(a,b)
    low = [q[-1]*(-1)**(len(q)-1) for q in seq]
    high = [q[0] for q in seq]
    return variations(low)-variations(high)


def routh_sign_changes(p):
    """All test cases avoid zero leading Routh entries."""
    p = list(map(F,p[::-1]))
    d = len(p)-1
    m = (d+2)//2
    a, b = p[::2], p[1::2]
    a += [F(0)]*(m-len(a))
    b += [F(0)]*(m-len(b))
    first = [a[0],b[0]]
    for _ in range(d-1):
        if not b[0]:
            return None
        row = [(b[0]*a[j+1]-a[0]*b[j+1])/b[0]
               for j in range(m-1)]+[F(0)]
        first.append(row[0])
        a,b = b,row
    if not all(first):
        return None
    return variations(first)


def run():
    rng = Random(563222)
    for ell in range(1,8):
        m = ell//2
        for k in range(2,9):
            for _ in range(3):
                w = [rng.randint(1,13) for _ in range(ell)]
                tau = rng.randint(1,59)
                a = spider(tau,[w]*k)
                n = k*(m+1) if ell%2 else k*m+1
                count = m+1 if k%2 else 2*m+1+(ell%2)
                check(len(a)-1 == n)
                check(count_negative(a) == count)
                check(count_negative(path(w[1:])) == m)
                if 1+ell*k <= 13:
                    check(brute(tau,[w]*k) == a)
    for _ in range(114):
        legs = [[rng.randint(1,50) for _ in range(rng.randint(1,5))]
                for _ in range(3)]
        tau = rng.randint(1,500)
        p = spider(tau,legs)
        check(routh_sign_changes(p) == 0)
        if 1+sum(map(len,legs)) <= 12:
            check(brute(tau,legs) == p)
    for k in range(4,13):
        tau = 1000**(k-1)
        p = spider(tau,[[1]]*k)
        n = routh_sign_changes(p)
        check(n is not None and n >= 2)
    print(f"Weighted spider fixtures passed: {checks} exact assertions.")


if __name__ == "__main__":
    run()
