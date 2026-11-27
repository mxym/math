#!/usr/bin/env python3
"""Cross-check exact finite interpolation identities and synthetic Airy asymptotics.

Run: python3 verify-one-sided-airy-padding.py
Needs SciPy (tested with 1.17). These checks supplement the analytic proof;
quadrature and finite-mesh convergence are not proofs or sampler benchmarks.
"""
from fractions import Fraction as F
from itertools import product
from math import exp, log, sqrt
from scipy.integrate import quad
from scipy.linalg import eigh_tridiagonal
from scipy.special import airy, ai_zeros, exp1


def exact_interpolants():
    cases = 0
    for k in range(1, 6):
        for v in product(range(4), repeat=k):
            norm = sum(a*a for a in v)
            if not norm:
                continue
            y = (0,) + v + (0,)
            for h in [F(1, 7), F(2, 5), F(3, 2)]:
                # b_j=v_j/sqrt(norm); the squared interpolant in a cell
                # is (y_i+(y_(i+1)-y_i)*t)^2/(norm*h), 0<=t<=1.
                mass, moment, energy, hat_mass, hat_moment = (F(0),) * 5
                for i, (a, b) in enumerate(zip(y, y[1:])):
                    u = b-a
                    poly = [a*a, 2*a*u, u*u]
                    hat = [a*a, b*b-a*a]
                    mass += sum(F(c, j+1) for j, c in enumerate(poly))/norm
                    moment += h/norm * sum(
                        c*(F(i, j+1)+F(1, j+2)) for j, c in enumerate(poly)
                    )
                    energy += F(u*u, norm)/h**2
                    hat_mass += sum(F(c, j+1) for j, c in enumerate(hat))/norm
                    hat_moment += h/norm * sum(
                        c*(F(i, j+1)+F(1, j+2)) for j, c in enumerate(hat)
                    )
                    if b:
                        assert F((a*a-b*b)**2, norm*b*b) == (
                            F((a-b)**2, norm) * (1+F(a,b))**2
                        )
                d = F(sum((a-b)**2 for a,b in zip(y,y[1:])), norm)
                overlap = F(sum(a*b for a,b in zip(y,y[1:])), norm)
                assert d/2 == 1-overlap
                assert energy == d/h**2
                assert hat_mass == 1 and hat_mass-mass == d/6
                assert moment <= hat_moment == h*F(
                    sum((j+1)*a*a for j,a in enumerate(v)), norm
                )
                cases += 1
    return cases


def integral(f, lo=0.0, hi=22.0):
    return quad(f, lo, hi, epsabs=2e-11, epsrel=2e-10, limit=400)[0]


def translate_losses(f, h):
    # Quadrature only; the omitted tails are negligible for the displayed
    # comparisons (but no tail certification is needed for the proof).
    boundary = integral(lambda x: f(x)**2, hi=h)/h**2
    def h_integrand(x):
        a, b = f(x), f(x+h)
        return ((a-b)/h)**2
    def c_integrand(x):
        a, b = f(x), f(x+h)
        return (((a-b)/h)*(1+a/b))**2
    return ((boundary+integral(h_integrand))/2,
            boundary+integral(c_integrand))


def numeric_airy():
    a = -ai_zeros(1)[0][0]
    k = 2*a/3
    n = sqrt(k)/abs(airy(-a)[1])
    f = lambda x: n*airy(k*x-a)[0]
    fp = lambda x: k*n*airy(k*x-a)[1]
    e = 4*a**3/27
    assert abs(integral(lambda x: f(x)**2)-1) < 1e-10
    assert abs(integral(lambda x: x*f(x)**2)-1) < 1e-10
    assert abs(integral(lambda x: fp(x)**2)-e) < 1e-10
    print("Airy exact targets, H^2/h^2 and chi^2/h^2:", e/2, 4*e)
    for h in [0.02, 0.01, 0.005, 0.002, 0.001, 0.0005]:
        he, ch = translate_losses(f,h)
        ga = translate_losses(lambda x: sqrt(27/2)*x*exp(-1.5*x),h)[1]
        gamma3_bound = (exp(3*h)*(1-3*h+1.5*(3*h)**2)-1)/h**2
        assert ga < gamma3_bound + 1e-7
        print(f"h={h:g}, Airy H^2/h^2={he:.10f}, chi^2/h^2={ch:.10f}, "
              f"Gamma3 chi^2/h^2={ga:.10f}")
    assert abs(he-e/2) < .005 and abs(ch-4*e) < .06 and abs(ga-9) < .2

    # Separate discrete Dirichlet spectral check, not a continuum certificate.
    errors = []
    for d in [8, 16, 32, 64]:
        h = 1/d
        diag = [2/h**2+k**3*j*h for j in range(1, 10*d)]
        off = [-1/h**2]*(len(diag)-1)
        eig = eigh_tridiagonal(diag,off,select="i",select_range=(0,0),
                              eigvals_only=True)[0]
        errors.append(abs(eig-a*k*k))
    assert all(b < a1 for a1,b in zip(errors,errors[1:]))
    assert errors[-1] < 4e-4
    print("Finite-mesh Dirichlet spectral errors:", errors)

    for u in [0.01,0.001,0.0001]:
        loss = exp(u)*(1-u+u*u*exp(u)*exp1(u))-1
        coeff = loss/(u*u*log(1/u))
        print(f"Gamma2 scaled shift u={u:g}: chi^2/(u^2 log(1/u))={coeff:.10f}")
    assert abs(coeff-1) < .13


if __name__ == "__main__":
    print("Exact rational interpolation checks:", exact_interpolants())
    numeric_airy()
    print("PASS")
