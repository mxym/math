#!/usr/bin/env python3
"""Exact small-instance checks for centered discrete-Gaussian membership."""
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import isqrt


def qvalue(Q, x):
    return sum(Q[i][j] * x[i] * x[j]
               for i in range(len(Q)) for j in range(len(Q)))


def mul2(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)


def ortho_projections_2(Q, upper):
    """I <= Q <= upper*I, hence every projection entry <= sqrt(upper)."""
    flat = sum(Q, ())
    cap = isqrt(upper)
    projections = []
    for E in product(range(-cap, cap+1), repeat=4):
        if mul2(E, E) == E:
            QE = mul2(flat, E)
            if QE[1] == QE[2]:
                projections.append(E)
    return projections


def independent(M, N, projections):
    return any(M((a,c)) and M((b,d))
               and N((1-a,-c)) and N((-b,1-d))
               for a,b,c,d in projections)


def fixture(Q, R=7):
    """All examples have integral Q >= I; the nome is 1/2."""
    n = len(Q)
    grid = list(product(range(-R, R+1), repeat=n))
    energies = [qvalue(Q,x) for x in grid]
    H = max(energies)
    weights = [1 << (H-e) for e in energies]
    scale = 1 << H
    # union over the first out-of-box coordinate in any position;
    # sum_{k>R} 2^{-k^2} <= 2^{1-(R+1)^2}, sum_{k in Z} 2^{-k^2} <= 3.
    tail = Fraction(n*4*3**(n-1), 2**((R+1)**2))
    return grid, weights, scale, tail


def check_pair(A, B, weights, scale, tail, truth):
    u = Fraction(sum(weights[i] for i in A), scale)
    v = Fraction(sum(weights[i] for i in B), scale)
    w = Fraction(sum(weights[i] for i in A & B), scale)
    total = Fraction(sum(weights), scale)
    # Covariance numerator is rho(A intersect B)rho(L)-rho(A)rho(B).
    lower = w*total-(u+tail)*(v+tail)
    upper = (w+tail)*(total+tail)-u*v
    if truth:
        assert lower <= 0 <= upper
    else:
        assert lower > 0, (float(lower), float(upper))
    return float(lower)


def hnf(a, b, c):
    # Columns (a,0), (b,c).
    return lambda x: x[1] % c == 0 and (x[0]-b*(x[1]//c)) % a == 0


def line(a, b):
    def contains(x):
        u, v = x
        if a != 0:
            return u % a == 0 and v == b*(u//a)
        return u == 0 and v % b == 0
    return contains


def inventory():
    # Retain HNF generators for the independent rotation-invariance test.
    groups = []
    for a,c in product(range(1,5), repeat=2):
        if a*c <= 12:
            for b in range(a):
                groups.append((hnf(a,b,c), ((a,0),(b,c))))
    for a,b in product(range(0,4), range(-3,4)):
        if a > 0 or a == 0 and b > 0:
            groups.append((line(a,b), ((a,b),)))
    groups.append((lambda x: x == (0,0), ()))
    return groups


def main():
    groups = inventory()
    n_zero = n_strict = n_ideal = 0
    minimum = 1.0
    Qlist = [
        (((1,0),(0,1)), 1, 4),
        (((2,0),(0,3)), 3, 4),
        (((3,1),(1,3)), 4, 2),
        (((2,2),(2,6)), 8, 4),
    ]
    for Q, upper, n_projections in Qlist:
        assert Q[0][0]-1 >= 0 and Q[1][1]-1 >= 0
        assert (Q[0][0]-1)*(Q[1][1]-1) >= Q[0][1]**2
        assert upper-Q[0][0] >= 0 and upper-Q[1][1] >= 0
        assert (upper-Q[0][0])*(upper-Q[1][1]) >= Q[0][1]**2
        Ps = ortho_projections_2(Q, upper)
        assert len(Ps) == n_projections
        grid, weights, scale, tail = fixture(Q)
        masks = [frozenset(i for i,x in enumerate(grid) if M(x))
                 for M,_ in groups]
        for a,b in combinations_with_replacement(range(len(groups)),2):
            truth = independent(groups[a][0], groups[b][0], Ps)
            lower = check_pair(masks[a], masks[b], weights, scale, tail, truth)
            if truth:
                n_zero += 1
            else:
                n_strict += 1
                minimum = min(minimum, lower)
        if Q == ((1,0),(0,1)):
            ideals = [j for j,(M,gens) in enumerate(groups)
                      if not(M((1,0)) and M((0,1)))
                      and all(M((-b,a)) for a,b in gens)]
            assert len(ideals) > 4
            for a,b in combinations_with_replacement(ideals,2):
                assert not independent(groups[a][0],groups[b][0],Ps)
                check_pair(masks[a],masks[b],weights,scale,tail,False)
                n_ideal += 1

    Q4 = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
    grid, weights, _, _ = fixture(Q4, R=4)
    law = {}
    for (u,v,w,z), mass in zip(grid, weights):
        state = ((u+v)%2 == 0, w%3 == 0, z%5 == 0)
        law[state] = law.get(state, 0) + mass
    T = sum(law.values())
    marg = [{bit:sum(m for s,m in law.items() if s[j] == bit)
             for bit in (False,True)} for j in range(3)]
    for state,mass in law.items():
        a,b,c = state
        assert mass*T*T == marg[0][a]*marg[1][b]*marg[2][c]
    assert len(law) == 8
    print(f"PASS: {n_zero} equality-compatible intervals, {n_strict} strict "
          f"pair intervals, {n_ideal} proper ideal pair intervals, "
          f"and {len(law)} exact joint masses (smallest strict lower "
          f"numerator {minimum:.3g}).")


if __name__ == "__main__":
    main()
