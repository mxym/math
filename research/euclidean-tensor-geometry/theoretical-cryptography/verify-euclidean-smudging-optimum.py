#!/usr/bin/env python3
"""Numerical and exact-rational cross-checks for Euclidean smudging envelopes.

Run with Python and SciPy (tested with 1.17). All cases are synthetic and
generated from the proof formulas; finite quadrature is not a proof.
"""
from fractions import Fraction as F
from math import comb, exp, pi, sqrt
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import betainc, gammaln, ndtr


def normal_density(q):
    return exp(-q*q/2)/sqrt(2*pi)


def constant(n):
    return exp(gammaln(n/2)-gammaln((n-1)/2))/sqrt(pi)


def sphere(n, u, h=1):
    b = h*h/(4*n)
    if u <= b:
        return 1.0
    return betainc(.5,(n-1)/2,b/u)


def derivative(n,u,h=1):
    b = h*h/(4*n)
    if u <= b:
        return 0.0
    return -constant(n)*sqrt(b)/u**1.5*(1-b/u)**((n-3)/2)


def root(n,h=1):
    return brentq(lambda u: sphere(n,u,h)-u*derivative(n,u,h)-1,
                  (h*h/12)*(1+1e-10),h*h*4,xtol=1e-14)


def envelope(n,u,h=1):
    w = root(n,h)
    if u >= w:
        return sphere(n,u,h)
    return 1+(sphere(n,w,h)-1)*u/w


def exact_odd_polynomials():
    cases = 0
    for m in range(20):
        n = 2*m+3
        poly = lambda t: sum(
            F((-1)**j*comb(m,j),2*j+1)*t**(2*j+1) for j in range(m+1)
        )
        normalization = poly(F(1))
        assert normalization > 0
        for j in range(1,10):
            t = F(j,11)
            value = poly(t)/normalization
            v = F(1,4*n)/t**2
            assert abs(sphere(n,float(v))-float(value))<3e-13
            cases += 1
    # n=3 uniform coordinate gives an exact root of the tangent equation.
    assert abs(root(3)-3/16)<1e-13
    return cases


def moments():
    cases = 0
    for n in range(1,37):
        odd_product = 1
        for k in range(1,13):
            odd_product *= 2*k-1
            # Integrate the unit-ball coordinate beta density by the even
            # moment ratio B(a+1,b)/B(a,b)=a/(a+b).
            scaled_moment = F(1)
            for j in range(k):
                scaled_moment *= F((n+2)*(2*j+1),n+2+2*j)
            assert scaled_moment <= odd_product
            assert (scaled_moment==odd_product) == (k==1)
            cases += 1
    return cases


def ball_slice_and_slope():
    cases = 0
    for d in range(1,18):
        for u in [0.12,0.75,1.35]:
            R = sqrt((d+2)*u)
            k = constant(d+2)
            density = lambda x: k/R*(1-(x/R)**2)**((d-1)/2)
            for h in [1,2**-14]:
                slab = quad(density,-min(h/2,R),min(h/2,R),
                            epsabs=1e-14,epsrel=1e-13)[0]
                assert abs(slab-sphere(d+2,u,h)) < 2e-12
                if h<1:
                    assert abs(slab/h-k/R) < 2e-8
                cases += 1
    return cases


def asymptotic():
    gs = brentq(lambda g:g*normal_density(g)-2*ndtr(-g),.2,sqrt(3),
                xtol=1e-14)
    vstar = 1/(4*gs*gs)
    print(f"Gaussian tangent gamma={gs:.12f}, u/h^2={vstar:.12f}")
    G = lambda v: 2*ndtr(1/(2*sqrt(v)))-1
    def A(v):
        g = 1/(2*sqrt(v))
        return normal_density(g)*(g**3-3*g)/2

    finite_count = 0
    max_err = 0
    for u in [0,0.03,0.10,0.99*vstar,vstar,1.01*vstar,.4,1,3]:
        if u <= vstar:
            base = 1+(G(vstar)-1)*u/vstar
            term = u*A(vstar)/vstar
        else:
            base,term = G(u),A(u)
        for n in [8,16,32,64,128,256,512,1024]:
            lo,hi = envelope(n,u),envelope(n+2,u)
            assert lo<=hi+3e-13
            assert abs(root(n)-vstar)*n < .4
            pred = base+term/n
            err = max(abs(lo-pred),abs(hi-pred))*n*n
            max_err = max(max_err,err)
            assert err < 2, (n,u,err)
            finite_count += 1
    print("Expansion and sandwich:", finite_count,
          "cases; maximum scaled residual", round(max_err,8))


def check_convex():
    count = 0
    for n in [3,4,5,11,26,101]:
        r = root(n)
        g = sphere(n,r)
        f = lambda v: 1+(g-1)*v/r if v<=r else sphere(n,v)
        for j in range(161):
            v = j*r/80
            assert f(v)<=sphere(n,v)+2e-14
            if j>0 and j<160:
                step = r/80
                assert 2*f(v)<=f(v+step)+f(v-step)+5e-14
            count += 1
    return count


if __name__=="__main__":
    print("Odd-dimensional exact polynomial vs beta:", exact_odd_polynomials())
    print("Exact bounded-ball subgaussian moments:", moments())
    print("Independent ball cross-sections and slope:", ball_slice_and_slope())
    print("Convex-envelope and chord grid:", check_convex())
    asymptotic()
    print("PASS")
