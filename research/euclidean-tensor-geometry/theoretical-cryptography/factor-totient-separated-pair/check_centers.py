"""Finite checks only. The inputs are labelled integer tuples, not moduli to factor."""
from itertools import product

def floor_ratio_root(top, bottom, power):
    lo, hi = 0, 1
    while hi**power * bottom <= top:
        hi *= 2
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if mid**power * bottom <= top:
            lo = mid
        else:
            hi = mid
    return lo

def sign_at(u, v, n, N, T):
    # x=u/v, enclose y=(N/x^2)^(1/n) within 1/L; all inequalities exact.
    L = 1 << 94
    h = floor_ratio_root(N*v*v*L**n, u*u, n)
    assert h > L
    a = (u-v)**2 * (h-L)**n - T*v*v*L**n
    b = (u-v)**2 * (h+1-L)**n - T*v*v*L**n
    assert a > 0 or b < 0
    return 1 if a > 0 else -1

def mul(seq):
    t = 1
    for x in seq:
        t *= x
    return t

counts = [0,0]
four = 0
for n, X, side, d, e in product(range(2,7), (10**6,10**7),
                                  (0,1), (1,5,11), (1,2,4)):
    a,b = ((2*X,5*X) if side == 0 else (5*X,2*X))
    P = (a-d,a+d+2)
    Q = tuple(b+e*(2*j-n+1) for j in range(n))
    N = mul(P+Q); T = mul(z-1 for z in P+Q); S = sum(P)
    # Endpoints S/2 +/- 1/8 have opposite signs with the correct orientation.
    left = sign_at(4*S-1,8,n,N,T)
    right = sign_at(4*S+1,8,n,N,T)
    assert (left,right) == ((-1,1) if side == 0 else (1,-1))
    D = mul(P)
    assert 4*D == S*S-(P[1]-P[0])**2
    assert mul(z-1 for z in P) == D-S+1
    counts[side] += 1
    if n == 2:
        c,b1 = S-1,sum(Q)-1
        assert b1*D*D-(N-T+c*b1)*D+c*N == 0
        four += 1
print("exact matched branches low/high:", *counts)
print("four-variable elimination identities:", four)
