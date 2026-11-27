#!/usr/bin/env python3
"""Exact modular Smith checks for the toroidal critical group formulas."""
from collections import Counter
from math import gcd

checks = 0


def eq(a, b):
    global checks
    checks += 1
    if a != b:
        raise AssertionError((a, b))


def smith_p(M, p, K):
    """Valuations below K, using unit elimination over Z/(p^K)."""
    Q = p**K
    M = [[x % Q for x in row] for row in M]
    n = len(M)
    result = []
    for k in range(n):
        pivot, best = None, K
        for i in range(k, n):
            for j in range(k, n):
                v = M[i][j]
                if not v:
                    continue
                e = 0
                while v % p == 0:
                    v //= p
                    e += 1
                if e < best:
                    best, pivot = e, (i, j)
                    if not best:
                        break
            if not best:
                break
        if pivot is None:
            return result + [None] * (n-k)
        result.append(best)
        d = p**best
        m = Q // d
        i, j = pivot
        M[i], M[k] = M[k], M[i]
        for row in M:
            row[j], row[k] = row[k], row[j]
        v = pow(M[k][k]//d, -1, m)
        for i in range(k+1, n):
            f = (M[i][k]//d)*v % m
            if f:
                for j in range(k+1, n):
                    M[i][j] = (M[i][j]-f*M[k][j]) % Q
            M[i][k] = 0
        # Column elimination of the rest of the pivot row no longer
        # changes the remaining submatrix, so it need not be performed.
    return result


def full(m, n):
    A = [[0]*(m*n) for _ in range(m*n)]
    for i in range(m):
        for j in range(n):
            k = i*n+j
            A[k][k] += 4
            for u, v in ((i+1, j), (i-1, j), (i, j+1), (i, j-1)):
                A[k][u % m*n+v % n] -= 1
    return A


def cprod(a, b, Q):
    n = len(a)
    c = [0]*n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    c[(i+j) % n] += x*y
    return [r % Q for r in c]


def transfer(m, b, K):
    Q = 2**K
    # Assign using additions so the cases m=1,2 count repeated steps.
    s = [0]*m
    s[0] = 4
    s[1 % m] -= 1
    s[-1] -= 1
    u, v = [0]*m, [1]+[0]*(m-1)
    for _ in range(b):
        uu, vv, uv = (cprod(u, u, Q), cprod(v, v, Q), cprod(u, v, Q))
        svv = cprod(s, vv, Q)
        u = [(x-y) % Q for x,y in zip(uu,vv)]
        v = [(2*x+y) % Q for x,y in zip(uv,svv)]
    u[0] -= 1
    w = [x+y for x,y in zip(u,cprod(s,v,Q))]
    V = [[u[(i-j)%m] for j in range(m)]+[-v[(i-j)%m] for j in range(m)]
         for i in range(m)]
    V.extend([[v[(i-j)%m] for j in range(m)]+[w[(i-j)%m] for j in range(m)]
              for i in range(m)])
    return V


def pp_div(n, p):
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a, n


def trim(a):
    while a and not a[-1]:
        a.pop()
    return a


def poly_gcd(a, b, p):
    a, b = trim([x % p for x in a]), trim([x % p for x in b])
    while b:
        r = a[:]
        inv = pow(b[-1], -1, p)
        while len(r) >= len(b):
            z = r[-1]*inv % p
            d = len(r)-len(b)
            for j,c in enumerate(b):
                r[d+j] = (r[d+j]-z*c) % p
            trim(r)
        a, b = b, r
    return a


def trace_poly(s, n, Q):
    """Trace C_n(s) with C_n(z+1/z)=z^n+1/z^n in the cyclic algebra."""
    l = len(s)
    A, B = [2]+[0]*(l-1), s[:]
    for _ in range(1, n):
        C = [(x-y) % Q for x,y in zip(cprod(s, B, Q), A)]
        A, B = B, C
    return B


def rankodd(m, n, p):
    a, m0 = pp_div(m, p)
    b, n0 = pp_div(n, p)
    A, B = p**a,p**b
    X = [-1]+[0]*(m0-1)+[1]
    s = [0]*m0
    s[0] = 4
    s[1 % m0] -= 1
    s[-1] -= 1
    f = trace_poly(s, n0, p)
    f[0] -= 2
    D = len(poly_gcd(X, f, p))-1
    yminus = len(poly_gcd(X, [1,-6,1], p))-1 if n0 % 2 == 0 else 0
    xminus = 2 if m0 % 2 == 0 and trace_poly([6], n0, p)[0] % p == 2 else 0
    regular = 2*D-2-xminus-2*yminus
    # (1,1) accounts for one pair; y=-1 has only one beta instead
    # of the normal two; both exceptional directions are smooth.
    origin = 2*min(A,B)-int(A==B)
    return origin + regular*min(A,B) + xminus*min(A,2*B) + yminus*min(2*A,B) - 1


def split_roots(p, d, K):
    """Prime-to-p roots of order dividing d (when d divides p-1)."""
    R = []
    for r in range(1, p):
        if pow(r, d, p) != 1:
            continue
        for k in range(2, K+1):
            Q = p**k
            r = (r - (pow(r, d, Q)-1)*pow(d*pow(r,d-1,Q), -1, Q)) % Q
        R.append(r)
    return R


def split_odd_exponents(p, m, n, K):
    b, n0 = pp_div(n,p)
    Q = p**K
    X, Y = split_roots(p,m,K), split_roots(p,n0,K)
    e = [b] if b else []
    for x in X:
        s = 4 - x - pow(x,-1,Q)
        for y in Y:
            k = (s - y - pow(y,-1,Q)) % Q
            if x == 1 and y == 1 or k % p:
                continue
            if not k:
                raise AssertionError("valuation exceeds precision")
            f = 0
            while k % p == 0:
                k //= p
                f += 1
            e.append(f+b)
            if y == Q-1 and b:
                e.append(b)
    return sorted(e)


def main():
    squares = {}
    for a in range(1, 7):
        M = transfer(2**a, a, 72)
        S = smith_p(M, 2, 72)
        eq(S.count(None), 1)
        eq(all(i > 0 for i in S if i is not None), True)
        trace = [x for x in S if x is not None]
        eq(len(trace), 2*2**a-1)
        eq(sum(trace), 2*2**a*(a+2)-6*a-1)
        squares[a] = trace
    exp_square = {
        1: [1,1,3], 2:[1,1,3,3,3,3,5],
        3:[1,1]+[3]*4+[5]*8+[7],
    }
    for a,S in exp_square.items():
        eq(squares[a], S)
    for a in range(1,6):
        for b in [a+1,a+3,a+6]:
            val = smith_p(transfer(1<<a,b,72),2,72)
            eq(val,[x+b-a for x in squares[a]]+[None])

    for m in range(1, 13):
        for n in range(m, 13):
            a,m0 = pp_div(m,2)
            b,n0 = pp_div(n,2)
            if a>b:
                a,b = b,a
            g = gcd(m0,n0)
            if not b:
                expected = [1]*(2*(g-1))
            else:
                core = [b] if not a else [x+b-a for x in squares[a]]
                expected = sorted(core+[b+2]*(2*2**a*(g-1)))
            sm = smith_p(full(m,n),2,48)
            eq(sm.count(None),1)
            eq([x for x in sm if x],expected)

    for p in [3,5,7,11]:
        for m in range(1, 11):
            for n in range(m, 11):
                sm = smith_p(full(m,n),p,1)
                eq(sm.count(None)-1,rankodd(m,n,p))
    for p,m,n,expected in [(3,4,6,[1]*3+[2]*2),
                            (5,6,10,[1]*3+[2]*2),
                            (7,3,14,[1]*3+[2]*2),
                            (3,4,12,[1]*3+[2]*4)]:
        sm = smith_p(full(m,n),p,20)
        eq(sm.count(None),1)
        eq([x for x in sm if x],expected)
    for p in [3,5,7,11,13,17,19]:
        for m in range(1, 11):
            for n in range(1, 15):
                b,n0 = pp_div(n,p)
                if (p-1) % m or (p-1) % n0:
                    continue
                sm = smith_p(full(m,n),p,20)
                eq(sm.count(None),1)
                eq([x for x in sm if x],split_odd_exponents(p,m,n,20))
    print(f"Toroidal sandpile checks passed: {checks} exact assertions.")
    for a,S in squares.items():
        print(f"base a={a}: {dict(sorted(Counter(S).items()))}")


if __name__ == "__main__":
    main()
