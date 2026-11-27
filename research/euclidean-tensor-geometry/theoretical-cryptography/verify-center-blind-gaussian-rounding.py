#!/usr/bin/env python3
"""Replay numerical and rational cross-checks for center-blind Gaussian rounding.

Requires mpmath. There is no external input, randomness, or network access.
The finite high-precision Fourier mesh is a cross-check, not a proof of TV.
"""
from fractions import Fraction as F
from math import floor
from mpmath import mp


def exact():
    n = 0
    for q in range(2, 51):
        for p in range(1, q):
            rho = F(p,q)
            b = 1-rho
            d = min(b/4,rho)
            plain = 1-rho*rho
            car = b*(1-d*d+rho*(1+d)**2)
            repair = b*(2-2*d)
            assert min(1,car,repair) > plain
            exp = lambda ell: b*(1-d*d+(ell-1-d)**2)
            assert exp(1) == b and exp(2) == repair
            for ell in range(3,13):
                assert exp(ell) > exp(ell-1)
            j = floor(1/rho)
            assert F(1,j+1)<rho<=F(1,j)
            # Root calculation with exact bracket signs.
            crossing = lambda x: j+(x-j)**2-rho*x*x
            assert crossing(j)>=0 and crossing(j+1)<0
            # The first frequencies after the crossing satisfy the inequality
            # in the same adjacent integer interval.
            lo,hi = F(j),F(j+1)
            for _ in range(12):
                mid = (lo+hi)/2
                if crossing(mid) < 0:
                    hi = mid
                else:
                    lo = mid
            assert crossing(lo)>=0 and crossing(hi)<0
            if rho < F(1,4):
                d = rho/b
                assert b*(1-d*d+rho*(1+d)**2)==1 and b*(1+d)==1
                assert b*(2-2*d)==2-4*rho>1
            n += 1
    return n


def realmat(rows):
    return mp.matrix(rows)


def theta_pairs():
    # A sheared lattice, a positive target covariance and both dual directions.
    basis = realmat([[2,1],[1,3]])
    target = realmat([[mp.mpf('1.2'),mp.mpf('.27')],
                      [mp.mpf('.27'),mp.mpf('.75')]])
    inv = target**-1
    counts = 0
    for coord in [0,1]:
        e = mp.eye(2)[:,coord]
        v = basis*e
        xi = (basis.T)**-1*e
        w = mp.pi*target*xi
        z = v/2+1j*w
        num = mp.exp(-(z.T*inv*z)[0]/2)
        assert abs(num) > mp.mpf('.05')
        for i in range(-3,4):
            for j in range(-3,4):
                y = basis*mp.matrix([i,j])
                d0,d1 = y-z, v-y-z
                f0,f1 = [mp.exp(-(d.T*inv*d)[0]/2) for d in (d0,d1)]
                assert abs((f0+f1)/f0) < mp.mpf('1e-65')
                counts += 1
    return counts


def to_mp(q):
    return mp.mpf(q.numerator)/q.denominator


def cos(x):
    return mp.cos(2*mp.pi*x)


def measure(t,rho,delta,N,first=False):
    t,rho,delta = to_mp(t),to_mp(rho),to_mp(delta)
    a = mp.exp(-2*mp.pi**2*t*t)
    b = 1-rho
    mod = 1+delta
    A = a**(b*(1-delta*delta))
    phi = lambda sd,x: mp.exp(-x*x/(2*sd*sd))/(mp.sqrt(2*mp.pi)*sd)
    r = mp.sqrt(b)*t
    shifts = range(-26,27)
    # Evaluate the partition directly, not by its claimed Fourier transform.
    table = []
    for i in range(N//2+1):
        x = mp.mpf(i)/N
        total = mp.fsum(phi(r,x-k)*(1-2*A*cos(mod*(x-k))) for k in shifts)
        assert total>0
        table.append(total)
    err = max(abs(v-1) for v in table)
    assert err < 20*a**(b*(2-2*delta))

    def coefficients(v):
        N = 2*(len(v)-1)
        return [
            (v[0]+(-1)**j*v[-1]+2*mp.fsum(v[i]*cos(mp.mpf(i*j)/N)
                           for i in range(1,N//2)))/N
            for j in range(N//2)
        ]

    # Compute only the small part 1/W0-1 to avoid precision loss.
    coeff = coefficients([1/y-1 for y in table])
    gaussian_norm = [mp.fsum(phi(r,mp.mpf(i)/N-k) for k in shifts)
                     for i in range(N//2+1)]
    ordinary = coefficients([1/y-1 for y in gaussian_norm])

    def expectation(freq,c):
        return a**(rho*b*freq*freq)*cos(freq*b*c)

    def vals(c):
        trigon = expectation(mod,c)
        ordinary_rel = 1+ordinary[0]+2*mp.fsum(
            u*expectation(j,c) for j,u in enumerate(ordinary) if j)
        raw_rel = 1-2*A*trigon
        adj = (1-2*A*trigon)*coeff[0]+2*mp.fsum(
            u*(expectation(j,c)-A*(expectation(j-mod,c)+expectation(j+mod,c)))
            for j,u in enumerate(coeff) if j
        )
        assert abs(adj) < 40*a**(b*(2-2*delta))
        return ordinary_rel, raw_rel+adj

    E = 2-4*rho if first else min(1,b*(1-delta**2+rho*mod**2),b*(2-2*delta))
    E0 = 1-rho*rho
    # Compare relative probabilities, then weight by the ordinary output density.
    # Summed TV uses only finite generated sites; unreported tails are immaterial
    # to a cross-check and are not an ingredient of the bounds in the note.
    eps,e0 = mp.mpf(0),mp.mpf(0)
    for c in [mp.mpf(0),mp.mpf(1)/7,mp.mpf(3)/7,mp.mpf(1)/2]:
        target = 1/mp.fsum(phi(t,c-k) for k in shifts)
        raw0 = raw1 = mp.mpf(0)
        for k in range(-12,13):
            k0,k1 = vals(c-k)
            g = phi(t,c-k)/2
            raw0 += g*abs(k0-target)
            raw1 += g*abs(k1-target)
        eps,e0 = max(eps,raw1),max(e0,raw0)
    assert eps < 50*a**E and e0 > a**E0/10
    return eps,e0,E


def coeff_examples():
    # Independently compute a Fourier coefficient of the reciprocal theta
    # and combine it with the shifted Gaussian transform. Work away from
    # integers; the dominant index changes exactly there.
    rows = []
    for rho in [F(2,3),F(1,2),F(2,7)]:
        r = to_mp(rho)
        j = floor(1/rho)
        edge = (j-mp.sqrt(j*(r*(j+1)-1)))/(1-r)
        xi = (edge+j+1)/2
        t = mp.mpf('1.3')
        a = mp.exp(-2*mp.pi**2*t*t)
        N = 50
        q = [1/(1+2*mp.fsum(a**(l*l)*cos(mp.mpf(i*l)/N)
                       for l in range(1,8))) for i in range(N)]
        coeff = [mp.fsum((u-1)*cos(mp.mpf(i*k)/N) for i,u in enumerate(q))/N
                 +(k==0) for k in range(8)]
        y = mp.fsum(coeff[abs(k)]*a**((xi-k)**2) for k in range(-7,8))
        ex = j+(xi-j)**2
        assert ex<r*xi*xi
        ratio = (-1)**j*y/a**ex
        assert abs(ratio-1)<mp.mpf('.12')
        rows.append(float(ratio))
    return rows


if __name__=="__main__":
    mp.dps = 90
    print("Exact rational exponent checks:", exact())
    print("Complex theta cancellation pairs:", theta_pairs())
    print("Dominant Fourier coefficient checks:", coeff_examples())
    for u,p,first in [(F(1),F(1,8),True),(F(5,4),F(1,3),False),
                       (F(5,4),F(1,2),False),(F(5,4),F(3,4),False)]:
        d = p/(1-p) if first else min((1-p)/4,p)
        eps0,raw0,ex0 = measure(u,p,d,24,first)
        eps1,raw1,ex1 = measure(u,p,d,36,first)
        assert ex0 == ex1
        assert abs(eps1-eps0)<max(eps1,mp.mpf('1e-55'))*mp.mpf('1e-12')
        assert abs(raw1-raw0)<max(raw1,mp.mpf('1e-55'))*mp.mpf('1e-12')
        assert eps1<raw1
        print("rho=%s: modulated=%s, ordinary=%s, guaranteed exponent=%.6f"
              % (p,mp.nstr(eps1,8),mp.nstr(raw1,8),float(ex1)))
    print("PASS")
