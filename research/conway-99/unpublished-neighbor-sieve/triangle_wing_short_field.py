"""Exact Hermite/Ihara bounds for each possible triangle-wing component size list."""
from fractions import Fraction as F
from math import prod


def partitions(n, k=1):
    if not n:
        yield ()
    for j in range(k, n+1):
        for rest in partitions(n-j, j):
            yield (j,)+rest


def tau_upper(k):
    if k == 1:
        return 75  # the six-vertex component is a prism
    n, u = 6*k, F(9, 20)
    h = (1-u)*(1-2*u)
    return 1/(n*(1-u*u)**(n//2)*u**(n-1)*h*
              (1+(n-1)*h/(3*n*u))**(n-1))


def bound(partition, rank):
    d = 7+len(partition)
    D = F(4, 9)*7**(rank-37+len(partition))*prod(map(tau_upper, partition))
    upper = 2**(d*(d-1))*D**7
    m = 2
    while m**(7*d) <= upper:
        m += 2
    return m-2


rows = []
for p in partitions(6):
    v = tuple(bound(p, r) for r in (36, 38, 40, 42))
    rows.append(v)
    print(p, v)
assert tuple(row[0] for row in rows) == (46, 52, 52, 58, 56, 62, 64, 68, 70, 68, 76)
print("worst case:", *(max(c) for c in zip(*rows)))
