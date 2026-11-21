"""Exact elimination controls; standard Python, including under python -O."""
from fractions import Fraction as F
from math import gcd, isqrt, prod


def check(condition, message):
    if not condition:
        raise ValueError(message)


def rref(a, columns):
    e = [[F(x) for x in row] for row in a]
    i = 0
    for j in range(columns):
        p = next((k for k in range(i, len(e)) if e[k][j]), None)
        if p is None:
            continue
        e[i], e[p] = e[p], e[i]
        e[i] = [x / e[i][j] for x in e[i]]
        for k in range(len(e)):
            if k != i and e[k][j]:
                e[k] = [x - e[k][j] * y for x, y in zip(e[k], e[i])]
        i += 1
    return i, e


def rows(n, ps):
    rows = []
    for p in ps:
        check(p > 2 and not any(p % d == 0 for d in range(2, isqrt(p) + 1)),
              ('prime', p))
        check(gcd(n, p) == 1, ('coprime', p))
        z = n - p
        a = []
        for q in ps:
            h = 0
            while z % q == 0:
                z //= q
                h += 1
            a.append(h)
        check(z == 1 and sum(a) >= 2, ('closed composite row', p))
        rows.append(a)
    for i in range(len(ps)):
        v = {i}
        while (w := v | {j for k in v for j, a in enumerate(rows[k]) if a}) != v:
            v = w
        check(len(v) == len(ps), ('strong connectivity', i))
    return rows


def affine(n, ps, s):
    a = rows(n, ps)
    k = len(ps)
    b, t = [0] * k, [[0] * (k-s) for _ in ps]
    for i, row in enumerate(a):
        check(sum(row[s:]) <= 1, ('outside multiplicity', ps[i]))
        h = prod(p**e for p, e in zip(ps[:s], row[:s]))
        if 1 in row[s:]:
            t[i][row[s:].index(1)] = h
        else:
            b[i] = h
    rank, e = rref([[int(i-s == j) + t[i][j] for j in range(k-s)]
                    + [1, -b[i]] for i in range(s, k)], k-s)
    check(rank == k-s, 'outside block invertibility')
    u = [row[-2] for row in e]
    v = [row[-1] for row in e]
    check([x*n + y for x, y in zip(u, v)] == ps[s:], 'outside recovery')
    rs = [1-sum(x*y for x,y in zip(t[i],u)) for i in range(s)]
    vs = [ps[i]+b[i]+sum(x*y for x,y in zip(t[i],v)) for i in range(s)]
    check(all(r != 0 and r*n == v for r,v in zip(rs,vs)), 'retained recovery')
    rank_b, _ = rref([[int(i == j)-x for j,x in enumerate(row)]
                      for i,row in enumerate(a)], k)
    return k-rank_b, rs, vs


check(affine(2200,[3,13],2) == (0,[1,1],[2200,2200]), 'true 2200')
for x in range(2,20):
    p = x-x**7  # P(x,0), from P(x,y)=x+y**3-y-x**7.
    check(p != 0 and p % (x*x) == x, ('specialized eliminant', x))
c, r, v = affine(128,[3,5,11,7,13,23,29,41],3)
check(c == 1 and r[:2] == [1,7] and v[:2] == [128,896], 'true 128')
rank, e = rref([[1,3,1],[5,1,1]],2)
check(rank == 2 and [row[-1]*217 for row in e] == [31,62], 'synthetic cycle')
print('2200 and 128 actual components, rank, affine recovery and cycle control: PASS')
