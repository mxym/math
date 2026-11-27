#!/usr/bin/env python3
"""Independent qubit check, with rational enclosures for spectra and logs."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import isqrt

ZERO = (F(0),)*3
I2_HALF = (F(1,2),F(0),F(1,2))
EPSILON = F(1,1 << 24)


def plus(A,B):
    return tuple(x+y for x,y in zip(A,B))


def scale(s,A):
    return tuple(s*x for x in A)


def total(X):
    R = ZERO
    for A in X:
        R = plus(R,A)
    return R


def psd(A):
    a,b,d = A
    return min(a,d) >= 0 and a*d >= b*b


@lru_cache(None)
def root(x):
    assert x >= 0
    den = 1 << 42
    q = isqrt(x.numerator * den**2 // x.denominator)
    lo = F(q, den)
    return lo, lo if lo**2 == x else F(q+1,den)


def discr(A):
    a,b,d = A
    return (a-d)**2+4*b*b


@lru_cache(None)
def norm(A):
    t = abs(A[0]+A[-1])
    a,b = root(discr(A))
    return max(t,a),max(t,b)


def log_series(y):
    assert 1 <= y <= 2
    z = (y-1)/(y+1)
    v = 2*sum(z**(2*i+1)/(2*i+1) for i in range(15))
    # This bounds the positive atanh-series tail by a geometric series.
    return v, v + 2*z**31/(31*(1-z*z))


LN2 = log_series(F(2))


@lru_cache(None)
def surprisal(x):
    assert 0 < x <= 1
    q,m = 1/x,0
    while q >= 2:
        q /= 2
        m += 1
    u,v = log_series(q)
    return m+u/LN2[1],m+v/LN2[0]


def entropy_term(L,H):
    assert 0 <= L <= H <= 1
    if H == 0:
        return F(0),F(0)
    if L == 0:
        assert H < F(1,3)
        return F(0),H*surprisal(H)[1]  # -x log2 x increasing here
    return L*surprisal(H)[0],H*surprisal(L)[1]


@lru_cache(None)
def S(A):
    assert psd(A)
    a,b,d = A
    t = a+d
    u,v = root(discr(A))
    high = entropy_term((t+u)/2,min(t,(t+v)/2))
    low = (F(0),F(0)) if a*d == b*b else entropy_term(max(0,(t-v)/2),(t-u)/2)
    return plus(high,low)


def interval_sum(items):
    lo = hi = F(0)
    for x,y in items:
        lo += x
        hi += y
    return lo,hi


def interval_sub(a,b):
    return a[0]-b[1],a[1]-b[0]


def diag_outputs(rows, f, M):
    blocks = [ZERO]*M
    for x,A in enumerate(rows):
        blocks[f[x]] = plus(blocks[f[x]],A)
    return blocks


def cq_side(groups, n):
    dists,cond = [],[]
    for blocks in groups:
        assert len(blocks) == n
        side = total(blocks)
        ideal = scale(F(1,n),side)
        assert all(psd(plus(side,scale(-1,A))) for A in blocks)
        dists.append(interval_sum(norm(plus(A,scale(-1,ideal))) for A in blocks))
        cond.append(interval_sub(interval_sum(map(S,blocks)),S(side)))
    lo,hi = interval_sum(dists)
    return (lo/2,hi/2),interval_sum(cond)


def scramble(rows, outputs):
    sizes = [max(dim)+1 for dim in zip(*outputs)]
    assert sizes == [2,4]
    raw = total(rows)
    raw_h = interval_sub(interval_sum(map(S,rows)),S(raw))
    cells = diag_outputs(rows,[a*4+b for a,b in outputs],8)
    # Indexed off-list groups built independently for each coordinate.
    group0 = [(cells[j],cells[j+4]) for j in range(4)]
    group1 = [cells[:4],cells[4:]]
    d0,h0 = cq_side(group0,2)
    d1,h1 = cq_side(group1,4)
    dj,hj = cq_side([cells],8)
    for d, h, m, ell in ((d0,h0,2,1),(d1,h1,4,2),(dj,hj,8,3)):
        u = 1-F(1,m)
        assert 0 <= d[0] <= d[1] <= u+EPSILON
        deficit = (ell*(1-d[1]/u),ell*(1-d[0]/u))
        residual = interval_sub(h,deficit)
        assert residual[1] >= 0 and residual[1]-residual[0] < EPSILON
    sharing = interval_sub(hj,interval_sum([h0,h1]))
    processing = interval_sub(raw_h,hj)
    assert sharing[1] >= 0 and processing[1] >= 0
    deficit = (3-2*d0[1]-F(8,3)*d1[1],3-2*d0[0]-F(8,3)*d1[0])
    residual = interval_sub(raw_h,deficit)
    assert residual[1] >= 0 and residual[1]-residual[0] < EPSILON
    return residual[0]>0


def tr_square(A):
    a,b,d = A
    return a*a+2*b*b+d*d


def leftover(rows):
    assert total(rows) == I2_HALF
    # Three independently chosen parity rows: 64 maps on F_2^2 -> F_2^3.
    masks = list(product(range(4),repeat=3))
    fs = [tuple(sum((((x & r).bit_count() & 1) << j) for j,r in enumerate(A))
                for x in range(4)) for A in masks]
    assert all(sum(f[x]==f[y] for f in fs)==8 for x,y in product(range(4),repeat=2) if x!=y)
    Q = 2*sum(map(tr_square,rows))
    coll = []
    errs = []
    for f in fs:
        C = diag_outputs(rows,f,8)
        coll.append(2*sum(map(tr_square,C)))
        lo,hi = interval_sum(norm(plus(A,scale(-F(1,8),I2_HALF))) for A in C)
        errs.append((lo/2,hi/2))
    assert sum(coll)/64 == Q+(1-Q)/8
    # Verify the stronger collision-form bound, without SDP or an estimate of H_min.
    assert (sum(x[1] for x in errs)/64)**2 <= F(7,4)*Q
    print(f"quantum leftover check: {len(fs)} public maps, pair collisions 1/8, exact Q={Q}")


def main():
    rows = [(F(1,4),F(0),F(0)),(F(0),F(0),F(1,4)),
            (F(1,8), F(1,8), F(1,8)),(F(1,8),-F(1,8),F(1,8))]
    # [R_0,R_2]_{01} is nonzero; no common diagonalizing basis.
    assert (rows[0][0]-rows[0][2])*rows[2][1] != 0
    leftover(rows)
    # Dense two-key output map, and a many-to-one map reaching the same
    # labels with nontrivial raw fibers. The output alphabets stay fixed.
    rows2 = [scale(w,A) for A in rows for w in (F(1,3),F(2,3))]
    rows3 = [scale(F(1,8),(1,1,1)) for _ in range(4)]
    maps = [
        (rows,[(0,0),(0,1),(1,2),(1,3)]),
        (rows2,list(product(range(2),range(4)))),
        (rows2,[(0,0),(1,1),(0,3),(1,1),(1,2),(1,3),(0,1),(1,0)]),
        (rows3,[(0,0),(0,1),(1,2),(1,3)]),
    ]
    strict = sum(scramble(raw,f) for raw,f in maps)
    assert strict == 4
    # Exact norm endpoints, and a noncommuting matrix difference with
    # an irrational norm, guard the sign convention and interval scale.
    assert norm((F(1,2),0,-F(1,2))) == (1,1)
    lo,hi = norm((F(1,2),F(1,2),-F(1,2)))
    assert lo**2 < 2 < hi**2 and hi-lo < EPSILON
    print(f"quantum entropy budget: {len(maps)} qubit models (3 noncommuting, 1 singular), {strict} certified strict via rational intervals")
    print("quantum controls: PSD domination, trace-norm conventions, entropy chain, and logarithm enclosures PASS")


if __name__ == "__main__":
    main()
