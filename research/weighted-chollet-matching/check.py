"""Exact, bounded diagnostics, not a premise of the proofs in paper.tex.

Usage: python3 check.py (Python 3.9+; no packages or network access).
"""
from itertools import combinations, permutations, product
from math import prod


def per(a):
    n = len(a)
    return sum(prod(a[i][j] for i, j in enumerate(p)) for p in permutations(range(n)))


def per_subsets(a):
    # Ryser's formula, independent of the permutation-sum routine.
    n = len(a)
    return sum((-1)**(n-len(s))*prod(sum(row[j] for j in s) for row in a)
               for k in range(n+1) for s in combinations(range(n), k))


def sq(a):
    return [[v*v for v in row] for row in a]


def lap(weights):
    a = [[0]*4 for _ in range(4)]
    for (i,j), w in zip(combinations(range(4),2), weights):
        a[i][i] += w
        a[j][j] += w
        a[i][j] = a[j][i] = -w
    return a


def require(statement, msg):
    if not statement:
        raise ValueError(msg)


def main():
    vertices = tuple(range(4))
    sets = [s for k in range(5) for s in combinations(vertices,k)]
    checks = 0
    for weights in product(range(3), repeat=6):
        a = lap(weights)
        for shift in [(0,0,0,0), (1,0,2,1)]:
            for s in sets:
                x = [[a[i][j] + (shift[i] if i == j else 0) for j in s] for i in s]
                p = per(x)
                q = per(sq(x))
                h = prod(a[i][i]+shift[i] for i in s)
                require(q <= p*h <= p*p, (weights,shift,s))
                checks += 1
    a = lap((1,2,3,4,5,6))
    p, q = per(a), per(sq(a))
    h = prod(a[i][i] for i in vertices)
    require((p,q,h*p) == (15232,114290848,153538560), 'weighted K4 example')
    require((p,q) == (per_subsets(a),per_subsets(sq(a))), 'independent K4 expansion')
    print('Weighted K4 permanents and strong upper bound:', p, q, h*p)
    print('Verified principal-set/diagonal-shift cases:', checks)


if __name__ == '__main__':
    main()
