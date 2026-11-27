#!/usr/bin/env python3
"""Independent polynomial reduction, kernel normals and character sums."""
from collections import Counter
from hashlib import md5, sha256
from pathlib import Path
import sys

N = 1024
P = 0x409


def rem(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def gcd(a, b):
    while b:
        a, b = b, rem(a, b)
    return a


def multiply(u, v):
    a = 0
    while u:
        bit = u & -u
        a ^= v << (bit.bit_length() - 1)
        u ^= bit
    return rem(a, P)


def frob(u, n):
    for _ in range(n):
        u = multiply(u, u)
    return u


def trace(u):
    s = 0
    for _ in range(10):
        s ^= u
        u = multiply(u, u)
    assert s <= 1
    return s


def cube(u):
    return multiply(u, multiply(u,u))


def dot(a,b):
    return (a&b).bit_count()&1


def solve_rank(rows):
    p = {}
    for row in rows:
        while row:
            j = row & -row
            if j not in p:
                p[j] = row
                break
            row ^= p[j]
    return len(p)


def direct_masks(pi, masks):
    """Compute mod-16 Walsh *differences* using the Walsh difference identity.
    W(u,v)-W(0,v) = -2 sum_{x: dot(x,u)=1} (-1)^dot(v,pi(x)).
    """
    n = len(pi).bit_length()-1
    out = []
    for mu in masks:
        points = [pi[x] for x in range(len(pi)) if dot(mu,x)]
        diffs = [-2 * sum(1-2*((p>>k)&1) for p in points) for k in range(n)]
        assert all(d%8 == 0 for d in diffs)
        out.append(sum((d//8&1) << k for k,d in enumerate(diffs)))
    return out


def polarization(f,x,y):
    return f[x]^f[y]^f[x^y]^f[0]


def compare_upstream(filename, t7):
    data = Path(filename).read_bytes()
    assert len(data) == 182023 and md5(data).hexdigest() == "56076503fa14e143df0151db3b378737"
    assert sha256(data).hexdigest() == "d829626bacfe76b8de55d41cec43edd1708e9984ece3f750692fd69623e0e0a0"
    lines = data.splitlines()
    assert len(lines) == 488
    upstream = [int(s, 16) for s in lines[3].split(b",") if s]
    assert upstream == t7
    print("upstream check: 488 rows, packaged polynomial matches all 128 entries in row 4")


def main():
    # Rabin irreducibility criterion, using prime divisors of 10.
    assert frob(2,10)==2
    assert gcd(P, frob(2,5)^2) == gcd(P, frob(2,2)^2) == 1
    assert multiply(2, 0x204)==1
    tr_masks = [sum(trace(multiply(u,1<<i))<<i for i in range(10)) for u in range(N)]
    assert len(set(tr_masks)) == N
    inv = [0]*N
    for d in range(1,N):
        if not inv[d]:
            d_inv = 1
            # 1022 = (1111111110)_2.
            for j in range(1,10):
                d_inv = multiply(d_inv, frob(d,j))
            assert multiply(d,d_inv) == 1
            inv[d], inv[d_inv] = d_inv, d
    s = [multiply(8,cube(cube(x))) for x in range(N)]
    f = [cube(x) ^ (0x204 if trace(s[x]) else 0) for x in range(N)]
    pi = [0]*N
    for x in range(1,N):
        d = multiply(0x204, inv[cube(x)])
        c = s[x] ^ frob(s[x],9) ^ frob(s[x],8)
        pi[x] = multiply(inv[cube(x)], c if trace(d) else 1)
        images = [polarization(f,x,1<<i) for i in range(10)]
        assert solve_rank(images)==9 and pi[x] and all(not dot(tr_masks[pi[x]], y) for y in images)
    eps = direct_masks(pi,tr_masks)
    zeros = [x for x in range(N) if not eps[x]]
    assert zeros == [0, 1, 118, 166, 211, 226, 236, 237, 270, 290, 388, 492, 516, 612, 626, 695]
    print("n=10 adjoint zeros via kernel normals / direct character sums:", zeros)
    nu = tr_masks[1]
    pivot = (nu & -nu).bit_length()-1
    basis = [(1<<i) ^ (dot(nu,1<<i)<<pivot) for i in range(10) if i != pivot]
    assert solve_rank(basis) == 9 and all(not dot(nu,b) for b in basis)
    bet = [[polarization(f,x,y) for y in basis] for x in basis]
    ranks = [solve_rank(sum(dot(m,z)<<j for j,z in enumerate(row)) for row in bet)
             for m in tr_masks]
    g = [int(r==8) for r in ranks]
    assert Counter(ranks) == Counter({8:938,6:85,0:1})
    assert all(sum(g[x] for x in range(N) if ((x>>j)&1)==0)%2==0 for j in range(10))
    assert sum(g)%2 == 0 and sum(g[:256])%2 == 1
    gs = sha256(bytes(g)).hexdigest()
    assert gs == "28363cbe8862c91670ba15ae1ed0307aeaadc8abf569978cbf96f1f23b1eca52"
    print("n=10 near-bent polar ranks:", sorted(Counter(ranks).items()),
          "; all ten coordinate hyperplane weights even; coordinate 8-flat weight",
          sum(g[:256]), "odd")

    # Expand the seven-variable quadratic using the triangular coefficient rows.
    tri = [[1,2,4,8,16,64],[4,6,16,24,44],[8,32,64,53],[64,97,69],[42,110],[111]]
    b7 = [[0]*7 for _ in range(7)]
    for i,row in enumerate(tri):
        for j,val in enumerate(row, i+1):
            b7[i][j] = b7[j][i] = val
    f7 = [0]*128
    for x in range(1,128):
        j = x.bit_length()-1
        y = x^(1<<j)
        f7[x] = f7[y]
        for i in range(j):
            if y>>i&1:
                f7[x] ^= b7[i][j]
    if len(sys.argv)>1:
        compare_upstream(sys.argv[1],f7)
    pi7 = [0]*128
    for x in range(1,128):
        cols = []
        for row in b7:
            v = 0
            for i,b in enumerate(row):
                if x>>i&1:
                    v ^= b
            cols.append(v)
        assert solve_rank(cols)==6
        [pi7[x]] = [v for v in range(1,128) if all(not dot(v,b) for b in cols)]
    e7 = direct_masks(pi7,range(128))
    assert [x for x in range(128) if not e7[x]] == [0,77,111]
    print("n=7 adjoint zeros via kernel normals / direct character sums: [0, 77, 111]")
    # This is *not* an inverse-degree counterexample to Open Problem 5.7.
    assert len(set(pi7)) == 128
    top = []
    for mask in range(128):
        c = 0
        for b in range(128):
            if b & mask == b:
                c ^= pi7.index(b)
        if mask.bit_count()==3: top.append(c)
        if mask.bit_count()>3: assert c==0
    assert solve_rank(top) == 7
    print("n=7 inverse-selector cubic ANF coefficient rank=7")
    print("PASS: independent degree and adjoint certificates")


if __name__=="__main__":
    main()
