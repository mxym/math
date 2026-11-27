#!/usr/bin/env python3
"""Exact generated checks in Q(sqrt(-5)) for the class-carry projection proof."""
from fractions import Fraction as F
from itertools import product

# a+b*omega, omega^2=-5.
def k(a=0,b=0):
    return F(a),F(b)


def add(x,y):
    return x[0]+y[0],x[1]+y[1]


def sub(x,y):
    return x[0]-y[0],x[1]-y[1]


def mul(x,y):
    a,b = x
    c,d = y
    return a*c-5*b*d,a*d+b*c


def conj(x):
    return x[0],-x[1]


def norm(x):
    a,b = x
    return a*a+5*b*b


def div(x,y):
    n = norm(y)
    a,b = mul(x,conj(y))
    return a/n,b/n


def integral(x):
    return all(a.denominator==1 for a in x)


def in_ideal(x,c):
    assert c in (0,1)
    return integral(x) and (c==0 or (x[0]-x[1])%2==0)


def gens(c):
    return [k(1),k(0,1)] if c==0 else [k(2),k(1,1)]


def determinant(P):
    a,b,c,d = P
    return sub(mul(a,d),mul(b,c))


def verify_table():
    # 0 represents R, 1 represents I=(2,1+omega), and I^2=(2).
    table = {
        (0,0):(k(1),k(1),k(0),k(1)),
        (0,1):(k(1),k(2),k(0),k(1)),
        (1,0):(k(0),k(1),k(1),k(0)),
        (1,1):(k(1,-1),k(2),k(2),k(1,1)),
    }
    for (A,I),P in table.items():
        a,b,c,d = P
        C = (A+I)%2
        det = determinant(P)
        assert norm(b)>0 and norm(det)>0
        # Check inclusion of an additive basis of the right side of (4).
        assert all(in_ideal(mul(a,g),A) and in_ideal(mul(b,g),I)
                   for g in gens(0))
        assert all(in_ideal(mul(c,g),A) and in_ideal(mul(d,g),I)
                   for g in gens(C))
        # Equal covolume, so inclusion is equality.
        assert norm(det)*2**C==2**(A+I)
        # N=20 is an allowed translation for the ratio representatives.
        assert all(in_ideal(mul(k(20),g),A) for g in gens(I))
    return table


def verify_wedge(table):
    count = 0
    for (A,I),(a,b,c,d) in table.items():
        det = determinant((a,b,c,d))
        for gx,gy,w,p in product([F(-1),0,F(1)], [F(-1,2),0,F(1,2)],
                                 [F(1,13),F(2,5),3,9],
                                 [F(1,19),F(1,7),2,18]):
            # Coordinates of the two vectors after projection off the already
            # emitted free span: (w,0) and ((20+gamma)*w,p).
            z = k(20+gx,gy)
            f = (mul(add(a,mul(b,z)),k(w)),mul(b,k(p)))
            g = (mul(add(c,mul(d,z)),k(w)),mul(d,k(p)))
            fn = sum(norm(x) for x in f)
            gn = sum(norm(x) for x in g)
            ip = add(mul(conj(f[0]),g[0]),mul(conj(f[1]),g[1]))
            assert norm(add(div(a,b),z))>=1
            assert fn>=norm(b)*w*w and fn>=norm(b)*p*p
            residual = gn-norm(ip)/fn
            assert residual==norm(det)*(w*p)**2/fn
            assert residual<=norm(det)/norm(b)*p*p
            count += 1
    return count


def diagonal_lower():
    # Q(sqrt(-5)) canonical squared norm equals 2 times the field norm.
    checks = 0
    mu = {}
    for x,y in [(1,0),(0,1),(1,1)]:
        values = sorted(
            2*norm(k(F(x+2*a,2),F(y+2*b,2)))
            for a,b in product(range(-3,4),repeat=2)
        )
        mu[x,y] = values[0]
        checks += len(values)
    assert mu=={(1,0):F(1,2),(0,1):F(5,2),(1,1):F(3)}
    for r in range(4,31):
        # Each vector outside R^r stays in one nonzero residue per coordinate.
        assert min(mu.values())*r>=2
        # The indicated explicit half-vector attains the diagonal threshold.
        assert sum(2*norm(k(F(1,2))) for _ in range(r))==F(r,2)
        checks += 1
    return checks


if __name__=="__main__":
    table = verify_table()
    print("Exact Steinitz class-transition tables:",len(table))
    print("Exact projected Hermitian wedge bounds:",verify_wedge(table))
    print("Diagonal-overlattice quadratic tests:",diagonal_lower())
    print("PASS")
