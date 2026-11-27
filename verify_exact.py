"""Exact checks in the power basis of a totally real cubic order."""

from itertools import combinations, product
from math import gcd, isqrt

P = 3578681
XS = ((0,0,0), (0,0,1), (1,0,0), (-1,0,0), (1,0,1), (2,0,0))
Z = (0,0,0)
E = ((1,0,0),(0,1,0),(0,0,1))


def f(x):
    return x**3 - 19*x + 11


def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def mul(a,b):
    q = [0]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            q[i+j] += x*y
    for j in (4,3):
        q[j-2] += 19*q[j]
        q[j-3] -= 11*q[j]
    return tuple(q[:3])


def det(a,b,c):
    return a[0]*(b[1]*c[2]-b[2]*c[1]) - b[0]*(a[1]*c[2]-a[2]*c[1]) + c[0]*(a[1]*b[2]-a[2]*b[1])


def norm(a):
    return det(*(mul(a,b) for b in E))


def reduced(v):
    return tuple(x % P for x in v)


def vsub(a,b):
    return tuple(reduced(sub(x,y)) for x,y in zip(a,b))


def symbol(coeff,x):
    out = []
    for dim in range(2):
        v = Z
        for a in reversed(coeff):
            v = add(mul(v,x),(a[dim],0,0))
        out.append(reduced(mul(v,x)))
    return tuple(out)


def level(pat):
    # All diagonal entries are 0 or 1. If a nonzero coordinate occurs
    # in an R-vector of squared length 1, every embedding has magnitude
    # <=1; its nonzero integral norm forces all magnitudes to be 1.
    # Hence that coordinate is ±1 and the remaining coordinate is 0.
    unit = ((1,0),(-1,0),(0,1),(0,-1))
    dot = lambda a,b: sum(x*y for x,y in zip(a,b))
    G = tuple(dot(a,b) for a in pat for b in pat)
    assert all(dot(a,a)==1 for a in pat)
    return [a for a in product(unit,repeat=len(pat))
            if tuple(dot(u,v) for u in a for v in a)==G]


def input_checks():
    assert all(f(x)%p for p in (2,3,5) for x in range(p))
    assert all(f(a)*f(b)<0 for a,b in ((-5,-4),(0,1),(4,5)))
    assert all(P%d for d in range(2,isqrt(P)+1))
    assert f(153)==P and (3*153**2-19)%P!=0
    assert P > 6*sum(26**i for i in range(1,5))
    abs_norms = [abs(norm(sub(v,u))) for u,v in combinations(XS,2)]
    assert all(0<m<P for m in abs_norms)
    for a,b,c in combinations(XS,3):
        M = [mul(sub(b,a),h) for h in E] + [mul(sub(c,a),h) for h in E]
        assert gcd(*(det(*cc) for cc in combinations(M,3))) == 1
    print(f"Cubic order: all 20 triple difference ideals are the unit ideal; "
          f"{sum(m>1 for m in abs_norms)}/15 pair differences are nonunits over R; "
          f"modulus P={P} has root 153 and is a nonfield quotient")


def exact(t,pat):
    F = level(pat)
    R = [tuple(symbol(a,x) for x in XS) for a in F]
    n = len(XS)
    pairs = {(i,j):{vsub(w[j],w[i]) for w in R}
             for i,j in combinations(range(n),2)}
    total = subsets = 0
    for size in range(t+1,n+1):
        for I in combinations(range(n),size):
            root = I[0]
            expected = {tuple(vsub(w[j],w[root]) for j in I[1:]) for w in R}
            assert len(expected) == len(F)
            found = {()}
            for j in I[1:]:
                found = {prefix+(z,) for prefix in found for z in pairs[root,j]
                         if all(vsub(z,y) in pairs[k,j] for k,y in zip(I[1:],prefix))}
            assert found == expected
            total += len(found)
            subsets += 1
    print(f"t={t}, Gram level size={len(F)}: {subsets} coordinate sets, "
          f"{total} normalized cliques, each extends uniquely")


def boundary_and_rate():
    # Two distinct whole-level pairs have Gram diag(25,25) with
    # offdiagonal zero, but one is outside the original T=4 box.
    pair_1 = ((3,4),(-4,3))
    pair_2 = ((5,0),(0,5))
    for a,b in (pair_1,pair_2):
        assert (sum(x*x for x in a),sum(x*y for x,y in zip(a,b)),
                sum(y*y for y in b)) == (25,0,25)
    assert max(abs(x) for row in pair_1 for x in row)==4
    assert max(abs(x) for row in pair_2 for x in row)==5
    # An explicit non-optimized size estimate for n=6,t=4 and eta=1/2.
    # Every basis coordinate of one product is bounded by M*T^2.
    t,L,s = 4,41,3
    M=max(sum(abs(mul(a,b)[r]) for a in E for b in E) for r in range(s))
    gram_levels_const=(2*L*M+1)**(s*t*(t+1)//2)
    N=max(abs(norm(sub(v,u))) for u,v in combinations(XS,2))
    C0_bound=31*7
    C1_bound=2*C0_bound*sum(26**i for i in range(1,t+1))
    prime_cap=2*(2+3*C1_bound+2*C0_bound+N)
    exponent_gap=2*(s*t*L-s*t*(t+1))-s*L*(2*t-1)
    assert exponent_gap==3
    # Squaring the desired |F| > q^(t-1/2) yields this integer inequality.
    const=gram_levels_const**2 * prime_cap**(s*L*(2*t-1))
    T=(1 << ((const.bit_length()+2)//3))
    assert T**3>const
    print(f"Whole-level boundary witness PASS; rate certificate t={t}, L={L}, eta=1/2: power gap={exponent_gap}")


if __name__ == "__main__":
    input_checks()
    base = ((1,0),(0,1),(-1,0),(0,1))
    for t in range(1,5):
        exact(t,base[:t])
    exact(4,((1,0),(-1,0),(1,0),(-1,0)))
    boundary_and_rate()
