#!/usr/bin/env python3
"""Exact rational replay of the finite sorted-support bounds for odd covers."""
from fractions import Fraction as F
from collections import defaultdict
import sys
from itertools import count
from math import isqrt, prod

if not __debug__:
    raise RuntimeError("Run without -O")

LIMIT = 168131152814625
RANK_LIMITS = {9: LIMIT, 10: 473824157932125, 11: 3506298768697725}

def primes():
    return (n for n in count(3, 2) if
            all(n % d for d in range(3, isqrt(n)+1, 2)))

def local_sum(p, a):
    return F(1, p-1) if a is None else F(p**a-1, (p-1)*p**a)

def loss(ps, caps, slots):
    """Two fixed anchors, then fixed tower-deletion flags and thresholds."""
    w = [local_sum(p, a) for p, a in zip(ps, caps)]
    g = [1/(1-w[i]) if i < 2 or slots[i-2][0] else F(1)
         for i in range(len(ps))]
    scales = [F(1), F(1)] + [1/(1-d) for delete, d in slots]
    u = [w[i]*g[i] for i in range(len(ps))]
    t = [d/u[i+2] + int(delete) for i, (delete, d) in enumerate(slots)]
    h = max(1, int(max(t, default=1)))
    mass, mean = {1: F(1)}, F(1)
    total = u[0]*u[1]
    for i, (p, a) in enumerate(zip(ps, caps)):
        if i >= 2:
            x = t[i-2]
            positive = mean - x + sum((x-v)*prob for v, prob in mass.items() if v < x)
            assert positive >= 0
            total += scales[i]*u[i]*positive
        if i+1 == len(ps):
            break
        gamma = scales[i]*g[i]
        assert gamma <= p
        def tail(k):
            return F(1) if k == 0 else (F(0) if a is not None and k>a else gamma/p**k)
        parts = [tail(d-1)-tail(d) for d in range(1,h+1)]
        z = {}
        for v, prob in mass.items():
            for d, part in enumerate(parts[:h//v], 1):
                if part:
                    z[v*d] = z.get(v*d, F(0)) + prob*part
        mass = z
        mean *= 1+gamma*w[i]
    return total

def finite_loss(ps, caps, slots):
    """Alternate replay: full product law and its direct positive-part sum."""
    weights = [sum((F(1,p**k) for k in range(1,a+1)),F(0))
               for p,a in zip(ps,caps)]
    mass = {1: F(1)}
    total = weights[0]*weights[1]/((1-weights[0])*(1-weights[1]))
    for i, (p,a,s) in enumerate(zip(ps,caps,weights)):
        delete, d = (True,F(0)) if i < 2 else slots[i-2]
        g = 1/(1-s) if delete else F(1)
        c = 1/(1-d)
        if i >= 2:
            total += c*sum(q*max(F(0),g*s*(x-int(delete))-d)
                           for x,q in mass.items())
        if i+1 == len(ps):
            break
        tails = [F(1)]+[c*g*F(1,p**k) for k in range(1,a+1)]+[F(0)]
        new = defaultdict(F)
        for j,(u,v) in enumerate(zip(tails,tails[1:]),1):
            for x,q in mass.items():
                new[x*j] += (u-v)*q
        assert sum(new.values()) == 1
        mass = new
    return total


def schedule(r, first=34):
    # Entries are in units of 1/200; 17/100 and 39/200 at p_3.
    raw = [(True, first), (True, 60), (True, 83),
           (False, 94), (True, 78)] + [(True, 100)]*max(r-7,0)
    return tuple((delete,F(d,200)) for delete,d in raw[:r-2])

def exponent_vectors(ps, limit):
    # Packed lcm = mandatory baseline times a product of extra prime powers.
    baseline = 3*prod(ps)
    cap = (limit-1)//baseline
    def rec(i, budget, prefix):
        if i == len(ps):
            yield prefix
            return
        p = ps[i]
        exponent = 2 if i == 0 else 1
        while budget >= 1:
            yield from rec(i+1, budget, prefix+(exponent,))
            budget //= p
            exponent += 1
    yield from rec(0, cap, ())

def ppm(q):
    return (q.numerator*10**6+q.denominator-1)//q.denominator

def main():
    gen = primes()
    ps = [next(gen) for _ in range(12)]
    assert min(RANK_LIMITS.values()) == LIMIT
    for r, limit in RANK_LIMITS.items():
        p = ps[:r]
        vectors = tuple(exponent_vectors(p,limit))
        assert len(set(vectors)) == len(vectors)
        def evaluate(a,slots):
            value = finite_loss(p,a,slots)
            if "--cross-check" in sys.argv:
                assert value == loss(p,a,slots)
            return value
        upper = max(min(evaluate(a,schedule(r)),evaluate(a,schedule(r,39)))
                    for a in vectors)
        print("rank",r,"vectors",len(vectors),"max ppm",ppm(upper),
              "rank-specific lcm lower bound",limit)
        assert upper < 1
    floor = 3*prod(ps)
    assert floor >= LIMIT
    print("rank >= 12 mandatory baseline:",floor)
    for r in (9,10,11):
        p = ps[:r]
        q = loss(p,(None,None)+(1,)*(r-2),schedule(r))
        print("rank",r,"no repeated primes beyond 5:",ppm(q))
        assert q < 1
    print("LCM lower bound",LIMIT)

if __name__ == "__main__":
    main()
