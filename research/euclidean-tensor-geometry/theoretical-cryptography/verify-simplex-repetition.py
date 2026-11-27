#!/usr/bin/env python3
"""Exact checks supporting the weak-correlation simplex expansion."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod


def check_covariance():
    C = 0
    for m in range(2, 18):
        # Rational Gram of normalized simplex directions; its rank
        # follows from (m/(m-1))*(I-J/m), an orthogonal projection.
        G = [[F(m*(i==j)-1, m-1) for j in range(m)] for i in range(m)]
        assert all(sum(row) == 0 for row in G)
        r = F(1, 2*(m-1))
        for i,j in product(range(m),repeat=2):
            GG = sum(G[i][k]*G[k][j] for k in range(m))
            assert GG == F(m,m-1)*G[i][j]
            mixed = (m-1)*r*G[i][j]+(1-(m-1)*r)*(i==j)
            assert mixed == (1 if i==j else -r)
            C += 1
    return C


def face_grid():
    count = 0
    for m in range(2, 8):
        k = m//2
        for u in product(range(-2,3),repeat=m):
            s = sum(u[i]*u[j] for i,j in combinations(range(m),2))
            assert s >= -4*k
            if m%2==0:
                listed = u.count(2)==k and u.count(-2)==k
            else:
                listed = u.count(2)>=k and u.count(-2)>=k
            assert (s==-4*k) == listed
            count += 1
    return count


def diagrams(m,u,v,p):
    E = tuple(combinations(range(m),2))
    # Edge pairs in the Taylor series, ordered and with factor 1/2.
    moments = [(p,u[i],v[i]) for i in range(m)]
    by_edges = F(0)
    for a,b in product(E,repeat=2):
        d = [0]*m
        for i in a+b:
            d[i] += 1
        by_edges += prod(moments[i][d[i]] for i in range(m))/2
    grouped = p**(m-2)*sum(v[i]*v[j]/2 for i,j in E)
    grouped += p**(m-3)*sum(v[i]*sum(u[j]*u[k] for j,k in E if i not in (j,k))
                            for i in range(m))
    grouped += 3*p**(m-4)*sum(prod(u[i] for i in I)
                              for I in combinations(range(m),4))
    assert by_edges == grouped
    return grouped


def check_second_order():
    count = 0
    p, a = F(1,2), F(2,3)
    for m in range(2,10):
        assert diagrams(m, tuple(F(i-3,11) for i in range(m)),
                        tuple(F(2*i-7,13) for i in range(m)), p) == diagrams(
                            m, tuple(F(i-3,11) for i in range(m))[::-1],
                            tuple(F(2*i-7,13) for i in range(m))[::-1], p)
        k = m//2
        u0 = (a,)*k+(-a,)*k
        q0 = 3*p**(m-4)*comb(k,2)*a**4
        if m%2==0:
            assert diagrams(m,u0,(F(0),)*m,p)==q0
            count += 1
        else:
            for uf,vf in product((F(-1,2),F(0),F(1,2)),repeat=2):
                assert diagrams(m,u0+(uf,),(F(0),)*(2*k)+(vf,),p)==q0-k*p**(m-3)*a*a*vf
                count += 1
    return count


def flips():
    M = 0
    for T,A,B in product(range(8),range(1,9),range(1,9)):
        assert abs(T+A-B) < T+A+B
        M += 1
    return M


if __name__=="__main__":
    c, f, s, h = check_covariance(), face_grid(), check_second_order(), flips()
    print(f"PASS: {c} exact standardized covariances, {f} first-order face checks, "
          f"{s} second-order coefficients, {h} balancing flips")
