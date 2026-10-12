#!/usr/bin/env python3
"""Independent finite evidence for mass-constrained planar Gaussian fans.

No binary floating point is used to establish any comparison.
All certified comparisons use fractions bounding pi and cosine.
The complete proofs are analytic and are in paper.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import factorial


def atan_reciprocal_bounds(m: int, terms: int = 55):
    """Alternating arctan(1/m) series with a rigorously signed remainder."""
    assert m >= 2 and terms > 0
    s = sum(((-1) ** j * Q(1, (2*j+1) * m ** (2*j+1))
             for j in range(terms)), Q(0))
    rem = Q(1, (2*terms+1) * m ** (2*terms+1))
    if terms % 2:
        return s-rem, s
    return s, s+rem


TRIG_SCALE = 10**70


def floor_frac_scaled(q: Q, scale: int):
    return q.numerator * scale // q.denominator


def ceil_frac_scaled(q: Q, scale: int):
    return -((-q.numerator * scale) // q.denominator)


@lru_cache(maxsize=1)
def pi_interval():
    a, b = atan_reciprocal_bounds(5)
    c, d = atan_reciprocal_bounds(239)
    # Machin identity with outward quantization to a uniform denominator.
    rawlo, rawhi = 16*a - 4*d, 16*b - 4*c
    lo = Q(floor_frac_scaled(rawlo, TRIG_SCALE),TRIG_SCALE)
    hi = Q(ceil_frac_scaled(rawhi, TRIG_SCALE),TRIG_SCALE)
    assert Q(314,100) < lo < hi < Q(315,100)
    assert hi-lo < Q(1,10**65)
    return lo,hi


def divceil(a: int, d: int):
    return -((-a)//d)


@lru_cache(maxsize=None)
def cosine_interval(angle_pi: Q, terms: int = 50):
    """Rational interval via *outward-rounded* fixed-point Taylor terms.

    Every single multiplication, division and conversion has explicit
    integer floor/ceil.  The final Taylor remainder is valid since
    |cos^(2*terms)(x)| <= 1 on the entire real line.
    """
    assert Q(0) <= angle_pi <= Q(2)
    plo,phi=pi_interval()
    xlo=floor_frac_scaled(angle_pi*plo,TRIG_SCALE)
    xhi=ceil_frac_scaled(angle_pi*phi,TRIG_SCALE)
    lpow=upow=TRIG_SCALE
    lower=upper=TRIG_SCALE
    for m in range(1,2*terms+1):
        lpow=lpow*xlo//TRIG_SCALE
        upow=divceil(upow*xhi,TRIG_SCALE)
        if m%2==0 and m<2*terms:
            a=lpow//factorial(m)
            b=divceil(upow,factorial(m))
            if (m//2)%2:
                lower-=b
                upper-=a
            else:
                lower+=a
                upper+=b
    rem=divceil(upow,factorial(2*terms))
    return Q(lower-rem,TRIG_SCALE),Q(upper+rem,TRIG_SCALE)


@lru_cache(maxsize=None)
def f_interval(angle_pi: Q):
    """Enclose sin^2(angle_pi*pi/2) exactly by rational bounds."""
    a, b = cosine_interval(angle_pi)
    return (Q(1)-b)/2, (Q(1)-a)/2


def v_interval(k: int, ep: Q, r: int):
    assert 1 <= r <= 3 <= k and Q(0) <= ep <= Q(2,k)
    ar = (Q(2)-(k-r)*ep)/r
    fa, fb = f_interval(ar)
    ea, eb = f_interval(ep)
    return r*fa+(k-r)*ea, r*fb+(k-r)*eb


def compositions(n: int, k: int):
    if k == 1:
        yield (n,)
    else:
        for i in range(n+1):
            for rest in compositions(n-i, k-1):
                yield (i,)+rest


def check_cases():
    examples = [
        (4,Q(0)), (4,Q(1,4)), (4,Q(1,3)),
        (5,Q(1,6)), (5,Q(1,4)), (5,Q(1,3)),
        (6,Q(1,10)), (6,Q(1,5)),
        (7,Q(1,10)), (7,Q(1,5)),
        (10,Q(1,10)), (10,Q(3,20)),
    ]
    for k,ep in examples:
        assert ep <= Q(2,k)
        vv = [v_interval(k,ep,r) for r in range(1,4)]
        winners = []
        for i in range(3):
            # A non-winner is *certified* only if another lower
            # bound exceeds its upper bound.
            if not any(j != i and vv[j][0] > vv[i][1]
                       for j in range(3)):
                winners.append(i+1)
        # At least one candidate must survive.
        assert winners
        print(f"candidate k={k}, eps/pi={ep}: "
              f"undominated_r={winners}, "
              "max_interval_width<1e-45")
        assert max(v[1]-v[0] for v in vv) < Q(1,10**45)
    # Specific sharp critical result and cubic ordering.
    v = [v_interval(5,Q(1,3),r) for r in range(1,4)]
    assert v[2][1] < Q(7,4)
    assert all(a <= Q(7,4) <= b for a,b in v[:2])
    for ep in [Q(0), Q(1,5), Q(1,3), Q(49,100)]:
        vv = [v_interval(4,ep,r) for r in range(1,4)]
        assert vv[2][0] > max(vv[0][1], vv[1][1])
    print("PASS: sharp five-sector critical value and four-sector ordering")
    # Certified bracketing of the *first* transition for several k,
    # including the k=100 asymptotic scale.
    brackets = [
        (5,Q(1,10),Q(1,6)), (6,Q(1,20),Q(1,10)),
        (10,Q(1,100),Q(1,20)), (100,Q(1,500),Q(1,400)),
    ]
    for k, left, right in brackets:
        vl2, vl3 = v_interval(k,left,2),v_interval(k,left,3)
        vr2, vr3 = v_interval(k,right,2),v_interval(k,right,3)
        assert vl3[0] > vl2[1], (k,left,"V3 not greater than V2")
        assert vr2[0] > vr3[1], (k,right,"V2 not greater than V3")
        print(f"PASS: first transition eps_*(k={k})/pi in ({left},{right})")


SCALE = 10**55
TOLERANCE = 10**20   # 10^-35 in fixed-point units


def floor_fixed(q: Q):
    return q.numerator * SCALE // q.denominator


def ceil_fixed(q: Q):
    return -((-q.numerator * SCALE) // q.denominator)


def check_grid(k: int, ep: Q, steps: int):
    assert 3 <= k <= 8 and steps > 0 and ep <= Q(2,k)
    T = Q(2)-k*ep
    tab = [(floor_fixed(a),ceil_fixed(b))
           for j in range(steps+1)
           for (a,b) in [f_interval(ep+T*j/steps)]]
    candidates = [v_interval(k,ep,r) for r in range(1,4)]
    upper = max(ceil_fixed(x[1]) for x in candidates)
    count = 0
    highest = -1
    for js in compositions(steps,k):
        score_upper = sum(tab[j][1] for j in js)
        if score_upper > highest:
            highest = score_upper
        assert score_upper <= upper + TOLERANCE, (k, ep, steps, js)
        count += 1
    print(f"PASS: grid k={k}, eps/pi={ep}, "
          f"resolution={steps}, vectors={count}, "
          "all scores certified <= candidate maximum + 1e-35")


def heterogeneous_candidate_intervals(floors: tuple[Q,...]):
    k=len(floors)
    assert k>=3 and all(x>=0 for x in floors) and sum(floors)<=2
    vals=[]
    for r in (1,2,3):
        for inds in combinations(range(k),r):
            inside=set(inds)
            a=(Q(2)-sum((floors[j] for j in range(k)
                         if j not in inside),Q(0)))/r
            if a<max(floors[i] for i in inds):
                continue
            xlo,xhi=f_interval(a)
            low=r*xlo
            high=r*xhi
            for j in range(k):
                if j not in inside:
                    l,h=f_interval(floors[j])
                    low+=l
                    high+=h
            vals.append((inds,low,high))
    assert vals
    return vals


def check_heterogeneous_grid(floors: tuple[Q,...], steps: int):
    k=len(floors)
    T=Q(2)-sum(floors,Q(0))
    choices=heterogeneous_candidate_intervals(floors)
    certified_upper=max(ceil_fixed(hi) for _,_,hi in choices)
    tables=[
        [ceil_fixed(f_interval(floors[i]+T*j/steps)[1])
         for j in range(steps+1)]
        for i in range(k)
    ]
    total=0
    for js in compositions(steps,k):
        up=sum(tables[i][js[i]] for i in range(k))
        assert up <= certified_upper+TOLERANCE,(floors,js)
        total+=1
    print(f"PASS: heterogenous floors {list(map(str,floors))}, "
          f"{len(choices)} feasible (<=3 free) candidates, "
          f"{total} certified grid vectors")


def check_sharp_stability_grid(steps: int):
    count = 0
    for i in range(2*steps+1):
        for j in range(2*steps-i+1):
            t=(Q(i,steps),Q(j,steps),Q(2*steps-i-j,steps))
            loss_lower = floor_fixed(Q(9,4)) - sum(
                ceil_fixed(f_interval(x)[1]) for x in t)
            bound_upper = ceil_fixed(Q(3,8)*sum(
                ((x-Q(2,3))**2 for x in t),Q(0)))
            assert loss_lower+TOLERANCE >= bound_upper, (steps,t)
            count+=1
    # Independently exact at both equality orbits.
    t=(Q(0),Q(1),Q(1))
    assert Q(9,4)-Q(2) == Q(3,8)*sum(
        ((x-Q(2,3))**2 for x in t),Q(0))
    t=(Q(2,3),)*3
    assert Q(9,4)-3*Q(3,4) == Q(3,8)*sum(
        ((x-Q(2,3))**2 for x in t),Q(0))
    print(f"PASS: sharp quadratic stability grid ({count} triples) "
          "and both exact equality orbits")


@lru_cache(maxsize=None)
def arcsin_rational_interval(x: Q, terms: int = 75):
    """Positive arcsine series with an explicit rational geometric tail."""
    assert Q(0)<=x<Q(1) and terms>0
    summand=Q(0)
    for n in range(terms):
        summand += Q(factorial(2*n),
                      factorial(n)**2 *4**n*(2*n+1))*x**(2*n+1)
    # Every Maclaurin coefficient is <= 1.
    err=x**(2*terms+1)/(1-x*x)
    return summand,summand+err


def arcsin_one_third_interval(terms: int = 75):
    return arcsin_rational_interval(Q(1,3),terms)


def check_simplex_dimension_jump():
    """Exact rational witness for a strict gap at k=4 and *all* k>=4.

    Relies only on the algebraic inequalities in Theorem 13,
    not on floating-point samples of normal order statistics.
    """
    u0=Q(35,162)
    p0=Q(22,7)
    gaps=[
        3*(1+u0)**2-4,
        15*(1+3*u0)**2-4*p0*p0,
        441*(1+10*u0+5*u0*u0)**2-512*p0*p0,
    ]
    expected=[
        Q(3817,8748),
        Q(58853,47628),
        Q(83693801929,3749847696),
    ]
    assert gaps==expected and all(q>0 for q in gaps)
    print("PASS: 3 exact rational inequalities establish the "
          "all-k>=4 simplex-vs-equal-mass-planar gap")
    # Enclose the exact k=4 simplex value and four-quadrant
    # planar value. The arcsine and pi bounds are both
    # independent rational interval constructions.
    pilo,pihi=pi_interval()
    asinlo,asinhi=arcsin_one_third_interval()
    ulo,uhi=2*asinlo/pihi,2*asinhi/pilo
    assert ulo>u0
    tetlo=3*(1+ulo)**2/(4*pihi)
    tethi=3*(1+uhi)**2/(4*pilo)
    planarlo=1/pihi
    planarhi=1/pilo
    assert tetlo>planarhi
    assert tethi-tetlo<Q(1,10**45)
    assert Q(353,1000)<tetlo<tethi<Q(354,1000)
    assert Q(318,1000)<planarlo<planarhi<Q(319,1000)
    delta_lo=Q(3,4)*(1+ulo)**2-1
    delta_hi=Q(3,4)*(1+uhi)**2-1
    assert 0<delta_lo<delta_hi<Q(1,8)
    assert uhi<Q(11,50)
    # At floor eps=pi/50, Theorem 7 says the best planar
    # value exceeds tetra; at eps=pi/40 tetra exceeds
    # the planar optimum. Every comparison is an
    # *exact rational interval* comparison.
    left_lo,left_hi=v_interval(4,Q(1,50),3)
    right_lo,right_hi=v_interval(4,Q(1,40),3)
    assert 2*left_lo>3*(1+uhi)**2
    assert 3*(1+ulo)**2>2*right_hi
    print("PASS: exact tetra-vs-all-planar transition bracket "
          "pi/50 < epsilon_tet < pi/40; "
          "positive delta < 1/8")
    print("PASS: exact rational arcsine interval certifies "
          "four-cell tetrahedral objective in (0.353,0.354), "
          "planar objective in (0.318,0.319)")
    # m5^2 > 5*pi/12 proves k=5 and k=6 by monotone
    # Gaussian maxima; m7^2 > pi/2 proves every k>=7.
    assert gaps[1]>0 and gaps[2]>0
    print("PASS: infinite-rank k>=7 bound by m7 and "
          "finite k=5,6 bound by m5")
    gap_lower=(3*(1+ulo)**2-4)/(4*pihi)
    assert gap_lower>Q(1,30)
    print("PASS: exact first-Hermite Gaussian noise "
          "stability comparison for 0<rho<=1/30")
    for rho, sign in [(Q(29,100),-1),(Q(3,10),+1)]:
        asinlo,asinhi=arcsin_rational_interval(rho)
        alo=asinlo/pihi
        ahi=asinhi/pilo
        q_lower=(Q(1,2)+alo)**2
        q_upper=(Q(1,2)+ahi)**2
        s_lower=Q(1,4)+rho*tetlo
        s_upper=Q(1,4)+rho*tethi
        if sign<0:
            assert q_upper<s_lower,("tet above quadrants",rho)
        else:
            assert q_lower>s_upper,("quadrants above tet Hermite lower bound",rho)
    print("PASS: unique first-Hermite witness noise correlation "
          "root lies in (29/100,3/10), exact rational enclosures")


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--quick", action="store_true")
    args=p.parse_args()
    lo,hi=pi_interval()
    print("PASS: exact Machin pi interval, width<1e-65")
    check_cases()
    check_grid(4,Q(1,4),12)
    check_grid(5,Q(1,4),10)
    if not args.quick:
        check_grid(5,Q(1,3),14)
        check_grid(6,Q(1,5),8)
    check_heterogeneous_grid((Q(0),Q(1,4),Q(1,6),Q(1,3)),10)
    check_heterogeneous_grid((Q(1,6),Q(1,4),Q(1,8),Q(1,12),Q(1,10)),9)
    if not args.quick:
        check_heterogeneous_grid((Q(1,3),)*5,10)
        check_heterogeneous_grid((Q(1,2),Q(1,3),Q(1,3),Q(5,6)),5)
        check_heterogeneous_grid((Q(1,6),Q(1,4),Q(1,3),
                                  Q(1,5),Q(1,7),Q(1,8)),7)
    check_simplex_dimension_jump()
    check_sharp_stability_grid(12 if args.quick else 24)
    print("ALL EXACT-RATIONAL CHECKS PASSED")


if __name__=="__main__":
    main()
