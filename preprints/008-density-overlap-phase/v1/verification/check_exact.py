#!/usr/bin/env python3
"""Independent exact finite regressions for density-overlap interpolation.

Standard-library integers and Fraction only. Checks the bounded-loss/root
inequality, signed-square change of variables, finite interpolation examples,
and a complete mass-matched multiscale convex-max construction by polygon
integration. These checks are not a formalization of the analytic theorem.

The finite 2D model has density x on (0,1)x(-1,1), NOT the smooth transverse
source in the manuscript. Rational hyperbola parametrizations make every
labeled mass equality exact. This tests the critical construction mechanism.
"""
from __future__ import annotations
import argparse
from bisect import bisect_right
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
import random

Point = tuple[Q, Q]
Plane = tuple[Q, Q, Q]
Polygon = tuple[Point, ...]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ArithmeticError(message)


def value(knots: list[Q], vals: list[Q], x: Q) -> Q:
    j = bisect_right(knots, x)-1
    return vals[j] if 0 <= j < len(vals) else Q(0)


def sqrt_upper(x: Q, denominator: int = 10**9) -> Q:
    """A certified rational upper bound; never a floating-point decision."""
    require(x >= 0, 'Square-root input')
    n = isqrt(x.numerator*denominator**2//x.denominator)
    if Q(n, denominator)**2 < x:
        n += 1
    answer = Q(n, denominator)
    require(answer**2 >= x, 'Upper square-root certificate')
    return answer


def overlap_checks(cases: int, seed: int = 8100726) -> dict:
    rng = random.Random(seed)
    root_count = identity_count = interpolation_count = 0
    for case in range(cases):
        knots = [Q(0)]+[Q(j, 20) for j in sorted(rng.sample(range(1, 20), 5))]+[Q(1)]
        us = sorted(Q(rng.randint(-20, 20), rng.randint(1, 4)) for _ in range(6))
        vs = sorted(Q(rng.randint(-20, 20), rng.randint(1, 4)) for _ in range(6))
        roots = [Q(rng.randint(0, 4)) for _ in range(6)]
        if not any(roots):
            roots[0] = Q(1)
        for s in (2, 3, 4):
            mass = sum((knots[j+1]-knots[j])*roots[j]**s for j in range(6))
            rho = [r**s/mass for r in roots]
            # Exact centered potential variance on the original intervals.
            f0 = Q(rng.randint(-2, 2))
            mean = square = X2 = U4 = V4 = Q(0)
            for j in range(6):
                l = knots[j+1]-knots[j]
                a, b, w = us[j], vs[j], rho[j]
                slope = a-b
                mean += w*(f0*l+slope*l*l/2)
                square += w*(f0*f0*l+f0*slope*l*l+slope*slope*l**3/3)
                X2 += w*l*slope*slope
                U4 += w*l*a**4
                V4 += w*l*b**4
                f0 += slope*l
            delta2 = square-mean*mean
            require(delta2 >= 0, 'Potential variance')
            for h in (Q(1, 100), Q(1, 10), Q(1, 2), Q(3, 2)):
                cuts = sorted({k+t for k in knots for t in (-h, Q(0), h)})
                loss_p = loss_m = root_diff = left = right = Q(0)
                for l, r in zip(cuts, cuts[1:]):
                    x, length = (l+r)/2, r-l
                    r0 = value(knots, rho, x)
                    rp = value(knots, rho, x+h)
                    rm = value(knots, rho, x-h)
                    if r0:
                        loss_p += length*r0*max(Q(0), 1-rp/r0)**s
                        loss_m += length*r0*max(Q(0), 1-rm/r0)**s
                    q0, qp = value(knots, roots, x), value(knots, roots, x+h)
                    root_diff += length*abs(q0-qp)**s/mass
                    z0, zp = value(knots, us, x), value(knots, us, x+h)
                    G0, Gp = z0*abs(z0), zp*abs(zp)
                    left += length*(Gp-G0)*min(r0, rp)
                    right += length*G0*(min(r0, rm)-min(r0, rp))
                require(loss_p <= s**s*root_diff, 'Forward loss/root inequality')
                require(loss_m <= s**s*root_diff, 'Backward loss/root inequality')
                require(left == right, 'Exact signed-square overlap identity')
                require(left >= 0, 'Monotone derivative increment sign')
                root_count += 2
                identity_count += 1
                if s == 2:
                    Xi = sqrt_upper(max(loss_p, loss_m))
                    rhs = 12*delta2/h**2+14*Xi*(sqrt_upper(U4)+sqrt_upper(V4))
                    require(X2 <= rhs, 'Overlap interpolation with certified norm bounds')
                    interpolation_count += 1
    return {'seed': seed, 'random_instances': cases, 'root_inequalities': root_count,
            'signed_square_identities': identity_count,
            'interpolation_inequalities': interpolation_count,
            'norm_bounds': 'certified rational upper bounds, not floating-point approximations'}


def clip(poly: Polygon, a: Q, b: Q, c: Q) -> Polygon:
    """Closed half-plane clipping; retains segments and points."""
    if not poly:
        return ()
    result = []
    previous = poly[-1]
    vp = a*previous[0]+b*previous[1]-c
    for current in poly:
        vc = a*current[0]+b*current[1]-c
        if (vp <= 0) != (vc <= 0):
            t = vp/(vp-vc)
            result.append((previous[0]+t*(current[0]-previous[0]),
                           previous[1]+t*(current[1]-previous[1])))
        if vc <= 0:
            result.append(current)
        previous, vp = current, vc
    return tuple(dict.fromkeys(result))


def integrate_x(poly: Polygon) -> Q:
    """Exact integral of the joint density x over a counterclockwise polygon."""
    if len(poly) < 3:
        return Q(0)
    total = Q(0)
    for (x, z), (y, t) in zip(poly, poly[1:]+poly[:1]):
        total += (x+y)*(x*t-y*z)/6
    require(total >= 0, 'Polygon orientation / nonnegative mass')
    return total


def cell(poly: Polygon, planes: list[Plane], index: int) -> Polygon:
    ai, bi, ci = planes[index]
    for j, (a, b, c) in enumerate(planes):
        if j != index:
            poly = clip(poly, a-ai, b-bi, ci-c)
            if not poly:
                break
    return poly


def planes_for(centers: list[Q], widths: list[Q], jumps: list[Q], tilt: Q) -> list[Plane]:
    """Descending centers; 2*jumps is the full slope jump at each cusp."""
    K = len(centers)
    require(centers == sorted(centers, reverse=True), 'Ordered cusp locations')
    require(all(r > 0 for r in jumps), 'Positive jumps')
    # Outer labels are ordered by the number of active positive-part summands.
    outer = [(Q(0), Q(0), Q(0))]
    slope = intercept = Q(0)
    for x, R in zip(centers, jumps):
        slope -= 2*R
        intercept += 2*R*x
        outer.append((slope, Q(0), intercept))
    central = []
    for n, (x, width, R) in enumerate(zip(centers, widths, jumps)):
        q = (outer[n][0]+outer[n+1][0])/2
        baseline = sum(2*jumps[j]*max(centers[j]-x, Q(0)) for j in range(K))
        central.append((q, R*tilt, baseline-q*x+R*width))
    return outer+central


def multiscale_case(K: int) -> dict:
    # beta=1, p=4. t_n=4^-n makes the jump t_n^-1/2 rational.
    t = [Q(1, 4**n) for n in range(1, K+1)]
    jumps = [Q(2**n) for n in range(1, K+1)]
    h = Q(1, 64*4**(2*K))
    b = h/4
    c = b*b/3
    L, R, ell, rr = [], [], [], []
    for x in t:
        a, d = 2*(x-h), 2*(x+h)
        L.append((a+c/a)/2)
        ell.append((a-c/a)/2)
        R.append((d+c/d)/2)
        rr.append((d-c/d)/2)
        require(L[-1]**2 == ell[-1]**2+c, 'Left exact smoothed-CDF matching')
        require(R[-1]**2 == rr[-1]**2+c, 'Right exact smoothed-CDF matching')
        require(0 < ell[-1]-b < rr[-1]+b < 1, 'Interior perturbed strip')
        require(ell[-1]+b < R[-1] and rr[-1]-b > L[-1], 'Common central overlap')
    for n in range(K-1):
        require(rr[n+1]+b < ell[n]-b, 'Disjoint neighboring strips')
    original_centers = [(l+r)/2 for l, r in zip(L, R)]
    shifted_centers = [(l+r)/2 for l, r in zip(ell, rr)]
    widths = [(r-l)/2 for l, r in zip(L, R)]
    shifted_widths = [(r-l)/2 for l, r in zip(ell, rr)]
    up = planes_for(original_centers, widths, jumps, Q(0))
    vp = planes_for(shifted_centers, shifted_widths, jumps, b)
    rectangle = ((Q(0), Q(-1)), (Q(1), Q(-1)), (Q(1), Q(1)), (Q(0), Q(1)))
    uc = [cell(rectangle, up, i) for i in range(len(up))]
    vc = [cell(rectangle, vp, i) for i in range(len(vp))]
    um = [integrate_x(poly) for poly in uc]
    vm = [integrate_x(poly) for poly in vc]
    require(sum(um) == sum(vm) == 1, 'Complete convex-cell partition masses')
    require(um == vm, 'Every labeled target mass matches exactly')
    require(all(m > 0 for m in um), 'Every listed atom active')
    joint = [[integrate_x(cell(uc[i], vp, j)) for j in range(len(vp))]
             for i in range(len(up))]
    require([sum(row) for row in joint] == um, 'Joint cell row marginals')
    require([sum(row[j] for row in joint) for j in range(len(vp))] == vm,
            'Joint cell column marginals')
    direct_cost = sum(joint[i][j]*((up[i][0]-vp[j][0])**2+(up[i][1]-vp[j][1])**2)
                      for i in range(len(up)) for j in range(len(vp)))
    predicted = coupling_upper = Q(0)
    for n, jump in enumerate(jumps):
        index = K+1+n
        m = um[index]
        require(m == R[n]**2-L[n]**2, 'Central interval mass')
        difference = 2*m-2*joint[index][index]
        require(difference > 0, 'Nonzero central mismatch')
        predicted += jump**2*difference+b*b*jump**2*m
        coupling_upper += b*b*jump**2*m
    require(direct_cost == predicted, 'Full map cost equals local symmetric-difference formula')
    direct_coupling = sum(um[i]*((up[i][0]-vp[i][0])**2+(up[i][1]-vp[i][1])**2)
                          for i in range(len(up)))
    require(coupling_upper == direct_coupling > 0, 'Exact labeled coupling upper cost')
    moments = [sum(m*(a*a+bb*bb)**2 for m, (a, bb, _) in zip(ms, ps))
               for ms, ps in ((um, up), (vm, vp))]
    M4 = max(moments)
    # After common normalization by M4^(-1/4), the sixth power of
    # (map_distance / coupling_upper_distance^(1/3)) is rational:
    ratio6 = direct_cost**3/(coupling_upper*M4)
    require(ratio6 > 0, 'Normalized sharpness quotient')
    return {'K': K, 'atoms_each': len(up), 'h': str(h), 'tilt_width': str(b),
            'all_label_masses_equal': True, 'joint_cells_checked': len(up)*len(vp),
            'map_cost_squared': str(direct_cost),
            'labeled_target_coupling_cost_squared': str(coupling_upper),
            'maximum_fourth_moment': str(M4),
            'normalized_quotient_sixth_power': str(ratio6),
            'quotient_sixth_power_over_K': str(ratio6/K),
            'scope': 'exact rational auxiliary model, not the theorem density or an infinite-limit certificate'}


def exponent_checks() -> list[dict]:
    answers = []
    for p in (Q(5, 2), Q(3), Q(4), Q(6), Q(10)):
        s = p/(p-2)
        beta = s-1
        alpha = (beta+1)*(p-2)/(2*p+(beta+1)*(p-2))
        require(alpha == Q(1, 3), 'Critical power agreement')
        require(beta*p/2 == beta+1, 'Logarithmic moment integral')
        require(Q(1, 2)/s-Q(1, 6)/s == Q(1, 3)/s, 'Critical log cost balance')
        require(Q(1, 3)/s == (p-2)/(3*p), 'Critical logarithmic exponent')
        answers.append({'p': str(p), 's': str(s), 'critical_beta': str(beta),
                        'critical_log_exponent': str(Q(1, 3)/s)})
    return answers


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', type=int, default=80)
    parser.add_argument('--max-scales', type=int, default=6)
    parser.add_argument('--output', type=Path, default=Path('verification/exact_checks.json'))
    args = parser.parse_args()
    if not 1 <= args.cases <= 1000 or not 1 <= args.max_scales <= 10:
        parser.error('Require 1<=cases<=1000 and 1<=max-scales<=10')
    overlap = overlap_checks(args.cases)
    print('PASS: bounded losses, root translations, signed-square identities and interpolation', flush=True)
    constructions = []
    for K in range(1, args.max_scales+1):
        row = multiscale_case(K)
        constructions.append(row)
        print(f'PASS: K={K}, {row["atoms_each"]} atoms, exact cell masses and map costs', flush=True)
    result = {'status': 'PASS', 'arithmetic': 'integers and Fraction only',
              'overlap': overlap, 'multiscale_constructions': constructions,
              'exponents': exponent_checks(),
              'scope': 'finite exact regressions; not independent peer review or proof-assistant formalization'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
