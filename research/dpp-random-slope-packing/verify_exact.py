#!/usr/bin/env python3
"""Enumerate all residues, bounded pairs and slope fibers (stdlib only)."""
from itertools import product


def floor_sum(n, m, a, b):
    ans = 0
    while True:
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        ans += qa * n * (n - 1) // 2 + qb * n
        top = a * n + b
        if top < m:
            return ans
        n, b = divmod(top, m)
        m, a = a, m


def count(p, t, z, a, b, lo, hi):
    top = b - a + 1
    assert 0 < top <= p
    n = hi - lo + 1
    u = t * lo - z
    return (floor_sum(n, p, t, u + b)
            - floor_sum(n, p, t, u + a - 1))


def unique(p, t, z, a, b, lo, hi):
    assert count(p, t, z, a, b, lo, hi) == 1
    left, right = lo, hi
    while left < right:
        mid = (left + right) // 2
        if count(p, t, z, a, b, lo, mid):
            right = mid
        else:
            left = mid + 1
    return a + ((z - t * left - a) % p), left


def main():
    floors = 0
    for n, m, a, b in product(range(10), range(1, 12), range(-8, 12),
                              range(-17, 18)):
        assert floor_sum(n, m, a, b) == sum((a*i+b)//m for i in range(n))
        floors += 1
    print(f"exact Euclidean floor sums: {floors} signed-offset cases")

    cases = fibers = recovered = ambiguous = fixed_answers = 0
    exact_traces = 0
    for p in (3, 5, 7, 11, 17, 23, 31, 43):
        cap = min(4, (p - 1)//4)
        for b1, b2 in product(range(cap+1), repeat=2):
            cases += 1
            rect = list(product(range(-b1,b1+1), range(-b2,b2+1)))
            point = {(a % p, b % p): (a,b) for a,b in rect}
            size = len(rect)
            difference_bound = (4*b1+1)*(4*b2+1)-1
            decisions = [[], []]  # global-good / fiber-local
            bads = 0
            for t in range(p):
                buckets = [[] for _ in range(p)]
                for a, b in rect:
                    buckets[(a+t*b)%p].append((a,b))
                bad = any(len(bucket) >= 2 for bucket in buckets)
                assert bad == (count(p,t,0,-2*b1,2*b1,-2*b2,2*b2) > 1)
                bads += bad
                test_glob = []
                test_loc = []
                for z, bucket in enumerate(buckets):
                    q = count(p,t,z,-b1,b1,-b2,b2)
                    fibers += 1
                    assert q == len(bucket)
                    if q == 1:
                        ans = unique(p,t,z,-b1,b1,-b2,b2)
                        assert ans == bucket[0]
                        recovered += 1
                    ambiguous += q >= 2
                    # An artificial transition predicate independent of input.
                    member = q == 1 and (ans[0]-2*ans[1]) % 3 == 0
                    test_glob.append(bad or member)
                    test_loc.append(q >= 2 or member)
                decisions[0].append(test_glob)
                decisions[1].append(test_loc)
            assert bads <= min(p,difference_bound)
            for a,b in product(range(p),repeat=2):
                truth = (a,b) in point and (point[a,b][0]-2*point[a,b][1])%3 == 0
                ga, la = (sum(tab[t][(a+t*b)%p] for t in range(p))
                          for tab in decisions)
                fixed_answers += 1
                if truth:
                    assert ga == la == p
                    exact_traces += 1
                elif (a,b) in point:
                    assert ga == bads and la <= min(p,size-1)
                else:
                    assert ga <= min(p,bads+size) and la <= min(p,size)
    print(f"exact box fibers: {cases} instances, {fibers} residue fibers; "
          f"{recovered} unique lifts, {ambiguous} ambiguous")
    print(f"exact fixed-answer checks: {fixed_answers} pairs; "
          f"{exact_traces} bounded acceptance cases preserve every slope")

    # If one ignores modulo reductions, a valid point can be lost.
    p, t, a, b = 43, 42, -2, 2
    z = (a+t*b) % p
    assert not (-3 <= z-t*b <= 3) and -3 <= a <= 3
    assert count(p,t,z,-3,3,-2,2) >= 1
    # An artificial predicate allowing only one of two same-fiber points:
    # no fixed tie choice can preserve both possible singleton predicates.
    t, z = 1, 0
    bucket = [(a,b) for a,b in product(range(-2,3),repeat=2)
              if (a+t*b)%43 == z]
    assert count(43,t,z,-2,2,-2,2) == len(bucket) == 5
    assert not all(bucket[0] in {honest} for honest in bucket)
    assert count(43,0,1,0,0,-2,2) == 0
    # Nonprime base ring need not have a unique slope (2t=0 mod 8).
    assert sum((2*t)%8 == 0 for t in range(8)) == 2
    print("negative controls: wraparound, tie-selection, empty fiber, "
          "nonfield direction all detected")
    print("PASS exact slope packing")


if __name__ == "__main__":
    main()
