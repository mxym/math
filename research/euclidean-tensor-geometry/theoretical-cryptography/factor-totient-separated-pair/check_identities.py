"""Labelled small-prime fixtures: verify divisibilities, not a factor recovery program."""
from itertools import combinations
from fractions import Fraction
from math import prod, gcd, isqrt

def prime(p):
    return p > 1 and all(p%i for i in range(2,isqrt(p)+1))
lo = (101,103,107,109,113,127)
hi = (601,607,613,617,619,631,641,643)
assert all(prime(x) for x in lo+hi)
branches = [0,0,0,0]
rest_checks = 0
for side in (0,1):
    A,B = (lo,hi) if side == 0 else (hi,lo)
    for n in range(2,6):
        for P in combinations(A,2):
            for Q in combinations(B,n):
                S,D = sum(P),prod(P)
                T = prod(x-1 for x in P+Q); N = D*prod(Q); g = gcd(N,T)
                assert all(z not in hi for z in P+Q if g%z == 0)
                if side == 0 and g != 1:
                    assert g == D or g in P
                    assert D in (g,g*(S-g))
                    branches[1 if g != D else 2] += 1
                else:
                    assert gcd(D,g) == 1
                    R = N//g; assert R%D == 0 and gcd(R,T) == 1
                    b = (S//2)**2; w = D-b
                    # Work only with this labelled identity, testing the full original modulus.
                    E = D-S+1
                    assert (w+b)%D == 0 and (w+b-S+1)%E == 0
                    assert gcd(D,E) == 1 and (N*T)%(D*E) == 0
                    c = b + R*((1-S)*pow(R,-1,T)%T)
                    assert gcd(c+w,N*T)%(D*E) == 0
                    assert -(P[1]-P[0])**2 == 4*w
                    branches[3 if g != 1 else 0] += 1
                H = prod(Q); K = prod(z-1 for z in Q)
                assert H*K*D*(D-S+1) == N*T and gcd(H,K) == 1
                for z in Q:
                    assert (H*K)%(z*(z-1)) == 0
                    rest_checks += 1
assert all(branches)
for k,expected in ((4,Fraction(3,4)),(5,Fraction(7,10)),(6,Fraction(2,3))):
    n = k-2
    A = min(Fraction(1,2),Fraction(4,k))
    B = min(Fraction(1,2),Fraction(2,n))
    assert (2+A+(n-1)*B)/k == expected
print("coprime/lower-single/lower-double/upper-noncoprime:", *branches)
print("labelled residual divisibilities:", rest_checks)
print("limiting shell exponents k=4,5,6: 3/4 7/10 2/3")
