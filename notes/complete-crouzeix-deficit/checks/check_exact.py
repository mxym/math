#!/usr/bin/env python3
"""Offline rational replay of algebra used in research.tex; not a proof assistant."""
from fractions import Fraction as F
import json

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def ident(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]

def transpose(a):
    return [list(row) for row in zip(*a)]

def mul(a, b):
    return [[sum((x*y for x,y in zip(row,col)), F(0))
             for col in zip(*b)] for row in a]

def add(a, b, sign=1):
    return [[x+sign*y for x,y in zip(ar,br)] for ar,br in zip(a,b)]

def scale(a, c):
    return [[c*x for x in row] for row in a]

def trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))

def hs2(a):
    return sum((x*x for row in a for x in row), F(0))

def unit_matrix(n, m, seed):
    """Rational stereographic unit vector, reshaped to an n by m matrix."""
    v = [F(((i+seed)*7 % 11)-5, 7) for i in range(n*m-1)]
    s = sum((x*x for x in v), F(0))
    coords = [2*x/(1+s) for x in v] + [(1-s)/(1+s)]
    a = [coords[i*m:(i+1)*m] for i in range(n)]
    require(hs2(a) == 1, 'stereographic normalization')
    return a

def block_case(n, m, amplitude, seed):
    a = [[F(0) for _ in range(n)] for _ in range(n)]
    a[0][1] = amplitude
    x,y = unit_matrix(n,m,seed),unit_matrix(n,m,seed+3)
    xt,yt = transpose(x),transpose(y)
    p0,q0,m0,l0 = mul(xt,x),mul(yt,y),mul(yt,x),mul(xt,y)
    p1,q1,m1,l1 = mul(mul(xt,a),x),mul(mul(yt,a),y),mul(mul(yt,a),x),mul(mul(xt,a),y)
    rho_x,rho_y = mul(x,xt),mul(y,yt)
    purity_x,purity_y,overlap = hs2(rho_x),hs2(rho_y),hs2(m0)
    require(hs2(p0) == purity_x and hs2(q0) == purity_y, 'density purity identity')
    require(trace(mul(rho_x,rho_y)) == overlap, 'density overlap identity')
    require(l0 == transpose(m0), 'constant Fourier term')
    diagonal = 4*(hs2(p0)+hs2(q0))+2*(hs2(p1)+hs2(q1))
    cross = 4*overlap+hs2(m1)+hs2(l1)
    energy = hs2(m0)+hs2(m1)
    slack = diagonal-2*cross
    require(cross == energy+3*overlap+hs2(l1), 'off-diagonal Parseval identity')
    d = add(rho_x,rho_y,-1)
    h = {-1:a,0:scale(ident(n),F(2)),1:transpose(a)}
    trace_laurent = sum((trace(mul(mul(mul(h[k],d),h[-k]),d)) for k in h), F(0))
    require(slack == trace_laurent, 'block trace = reduced-density trace')
    require(hs2(d) == purity_x+purity_y-2*overlap, 'density difference identity')
    mu = 2-amplitude
    cap = min(mu*mu,F(3))
    require(slack >= mu*mu*hs2(d), 'strict positive-block lower bound')
    require(slack+6*overlap >= cap*(purity_x+purity_y), 'rank-free slack')
    require((purity_x+purity_y)**2 >= 4*purity_x*purity_y, 'arithmetic/geometric mean')
    upper = 1+amplitude # triangle bound for the norm of R=I+lambda^{-1}A
    require(energy**2 <= upper**4*purity_x*purity_y, 'purity-weighted resolvent energy bound')
    # Exact algebra of the deficit; arbitrary X,Y here need not be singular vectors.
    gamma = amplitude
    dp = 4*energy/gamma**2-(4*hs2(p0)+2*hs2(p1))
    dq = 4*energy/gamma**2-(4*hs2(q0)+2*hs2(q1))
    require(2*energy*(4/gamma**2-1) == dp+dq+slack+6*overlap+2*hs2(l1), 'full deficit algebra')

def nilpotent_singular_case(t):
    energy,gamma = t*t,t
    dp,dq,slack = F(0),F(0),8-2*t*t
    require(2*energy*(4/gamma**2-1) == dp+dq+slack, 'actual nilpotent singular-pair deficit')
    require(slack > 0, 'strict nilpotent block slack')
    intrinsic_eta = min((2-t)**2,F(3))/(1+t)**2
    require(t*t*(1+intrinsic_eta) <= 4, 'intrinsic bound with rigorous upper bound on M')
    r = t/2
    geometric_eta = min(4*(1-r)**2/(1+2*r)**4,F(3))*(1-r)**2
    require(t*t*(1+geometric_eta) <= 4, 'geometric disk bound')
    for fraction in [F(0),F(1,10),F(1,3),F(1,2)]:
        e = fraction*(1-r)
        d,b,q,D = 1-r,1-r,F(1),1+t
        require(e < min(d,b/q), 'perturbation hypotheses')
        eta_e = min(4*(b-q*e)**2/(D+e)**4,F(3))*(d-e)**2/q**2
        require(eta_e > 0, 'positive perturbation gap')
        require(t*t*(1+eta_e) <= 4, 'zero-perturbation example obeys robust constant')

def main():
    blocks = 0
    for n,m in [(2,1),(2,2),(3,2),(4,3)]:
        for t in [F(1,4),F(1,2),F(1),F(3,2),F(7,4)]:
            for seed in range(1,6):
                block_case(n,m,t,seed)
                blocks += 1
    singular = 0
    for denominator in range(2,17):
        for numerator in range(1,2*denominator):
            nilpotent_singular_case(F(numerator,denominator))
            singular += 1
    require(8-2*F(2)**2 == 0, 'boundary nilpotent slack vanishes')
    require(F(4)/(1+min(F(4),F(3))) == 1, 'zero matrix intrinsic constant squared')
    print(json.dumps({
        'arithmetic':'fractions.Fraction; no floating point',
        'generic_rational_Laurent_block_cases':blocks,
        'actual_nilpotent_singular_pair_cases':singular,
        'perturbation_parameter_cases':4*singular,
        'boundary_and_zero_matrix_checks':2,
        'status':'PASS',
        'scope':'Algebra, constants, and explicit examples only. Analytic/universal proof is in research.tex.'
    },indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
