#!/usr/bin/env python3
"""Exact checks on fixed-size synthetic binary chain-ring probability spaces."""
from itertools import product
from math import prod
from random import Random

checks, evals = 0, 0
rng = Random(994601)


def check(ok):
    assert ok
    global checks
    checks += 1


def xor(xs):
    r = 0
    for x in xs:
        r ^= x
    return r


def mul(x, y, k):
    return xor(x << j for j in range(y.bit_length()) if y >> j & 1) & ((1 << k) - 1)


def zero(n, m):
    return [[0] * m for _ in range(n)]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def tr(A):
    return [list(r) for r in zip(*A)]


def plus(A, B):
    return [[a ^ b for a, b in zip(x, y)] for x, y in zip(A, B)]


def mat(A, B, k):
    return [[xor(mul(a, b, k) for a, b in zip(x, y)) for y in tr(B)] for x in A]


def rb(n, m, k):
    return [[rng.randrange(1 << k) for _ in range(m)] for _ in range(n)]


def random_invertible(n, k):
    A = eye(n)
    for _ in range(4 * n):
        i, j = rng.sample(range(n), 2)
        z = rng.randrange(1 << k)
        A[i] = [x ^ mul(z, y, k) for x, y in zip(A[i], A[j])]
    return A


def unit_inverse(x, k):
    assert x & 1
    y = x ^ 1
    p = t = 1
    for _ in range(k - 1):
        t = mul(t, y, k)
        p ^= t
    return p


def matrix_inverse(A, k):
    n = len(A)
    B = [row[:] + ident for row, ident in zip(A, eye(n))]
    for j in range(n):
        p = next(i for i in range(j, n) if B[i][j] & 1)
        B[j], B[p] = B[p], B[j]
        v = unit_inverse(B[j][j], k)
        B[j] = [mul(x, v, k) for x in B[j]]
        for i in range(n):
            if i != j:
                v = B[i][j]
                B[i] = [a ^ mul(v, b, k) for a, b in zip(B[i], B[j])]
    return [row[n:] for row in B]


def restrict(A, rr, cc, k):
    return [[A[i][j] & ((1 << k) - 1) for j in cc] for i in rr]


def schur(A, s, k):
    n, m = len(A), len(A[0])
    a, b, c = range(s), range(s,n), range(s,m)
    B, E = restrict(A,a,a,k), restrict(A,a,c,k)
    C, D = restrict(A,b,a,k), restrict(A,b,c,k)
    return plus(D,mat(mat(C,matrix_inverse(B,k),k),E,k))


def span_min(r):
    v = [sum(e << i for i, e in enumerate(row)) for row in r]
    return min(xor(v[j] for j in range(len(v)) if s >> j & 1).bit_count()
               for s in range(1, 1 << len(v)))


for n, m, k in [(2,2,3),(3,4,4),(4,4,6),(4,6,5),(5,5,6),(5,6,5)]:
    for _ in range(20):
        s = rng.randrange(1, min(n,m))
        P, Q = random_invertible(n,k), random_invertible(m,k)
        invP, invQ = matrix_inverse(P,k), matrix_inverse(Q,k)
        check(mat(P,invP,k)==eye(n) and mat(Q,invQ,k)==eye(m))
        base = [[2*v + int(i == j and i < s) for j,v in enumerate(row)]
                for i,row in enumerate(rb(n,m,k-1))]
        A = mat(mat(invP,base,k),invQ,k)
        L = restrict(P,range(s,n),range(n),1)
        R = restrict(Q,range(m),range(s,m),1)
        d = span_min(L)*span_min(tr(R))
        s0 = schur(base,s,k)
        check(all(not x & 1 for row in s0 for x in row))
        for j in range(1,k):
            Z = rb(n,m,1)
            new = plus(A,[[v << j for v in row] for row in Z])
            s1 = schur(mat(mat(P,new,k),Q,k),s,k)
            w = [[x << j for x in row] for row in mat(mat(L,Z,1),R,1)]
            check(restrict(plus(s0,s1),range(n-s),range(m-s),j+1)==w)
        dims = (n-s)*(m-s)
        if dims <= 9:
            best = n*m+1
            for a in range(1,1<<dims):
                A0 = [[a >> (i*(m-s)+j) & 1 for j in range(m-s)] for i in range(n-s)]
                dual = mat(mat(tr(L),A0,1),tr(R),1)
                weight = sum(map(sum,dual))
                check(weight>=d)
                best = min(best,weight)
            check(best==d)


def T_digits(coeff, B):
    # Expand (1+T)^i mod T^B.
    return xor(xor(1 << j for j in range(B) if j & i == j)
               for i in range(B) if coeff >> i & 1)


for B, d in [(1,4),(2,4),(4,4),(4,16),(8,8),(8,32)]:
    for a,b in [(2,1),(1,7),(3,3)]:
        plus_count = ((a+b)**(d//B)+(a-b)**(d//B))//2
        minus_count = ((a+b)**(d//B)-(a-b)**(d//B))//2
        high, low = max(plus_count,minus_count), min(plus_count,minus_count)
        w = [plus_count**(B-x.bit_count())*minus_count**x.bit_count() for x in range(1<<B)]
        digs = [T_digits(x,B) for x in range(1<<B)]
        check(len(set(digs)) == 1<<B)
        for j in range(B):
            weight = 1 << j.bit_count()
            toggle = T_digits(1<<j,B)
            check(digs[toggle] == 1<<j and toggle.bit_count() == weight)
            for h in range(1<<j):
                a0 = sum(w[i] for i,z in enumerate(digs) if z % (2<<j) == h)
                a1 = sum(w[i] for i,z in enumerate(digs) if z % (2<<j) == h+(1<<j))
                check(max(a0,a1)*low**weight <= min(a0,a1)*high**weight)


# Independent surjection enumeration on small spaces. If a truncated cokernel has
# a full-depth summand, there is a surjection onto the chain ring. Count those
# directly and compare to the existential flag and to the exact first moment.
for k,n,m in [(1,2,2),(2,2,2),(2,2,3),(3,2,2)]:
    ring = range(1<<k)
    balls = [(a,b) for a,b in product(ring,repeat=n) if (a|b)&1]
    choices = list(product(ring,repeat=n))
    tail = moment = 0
    for cols in product(choices,repeat=m):
        rv = sum(all(mul(a,x,k)^mul(b,y,k)==0 for x,y in cols) for a,b in balls)
        tail += int(rv>0)
        moment += rv
        check(not rv or rv >= 1<<(k-1))
        evals += 1
    check(moment == len(balls)*(1<<(k*m)))
    check(tail * (1<<(k*(m-n+1)-1)) <= len(choices)**m)

print(f'PASS: {checks} exact assertions and {evals} exhaustive Haar test matrices')
