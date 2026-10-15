"""Reviewer-written X controls. No author module/AST/execution is used.

Finite identities and samples support the separate analytic proof review.
They are not exhaustive quantum or scalar-maximization certificates.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def exact():
    import sympy as s
    t, h, a, k, z, m = s.symbols('t h a k z m', positive=True)
    variance = t*t*h*(1-h)/(1+t*h)**2
    assert s.factor(s.diff(variance, h)-t*t*(1-(t+2)*h)/(1+t*h)**3) == 0
    assert s.factor(variance.subs(h, 1/(t+2))-t*t/(4*(1+t))) == 0
    assert s.factor((t*t/(4*(1+t))).subs(t, 2/(m-1))-1/(m*m-1)) == 0
    # Differentiate the actual finite moment in k, with z=(1+k)^(a-1).
    numerator = 1+h*((1+k)*z-1)
    true_derivative = a*h*z/numerator-a*h/(1+k*h)
    complete = a*h*(1-h)*(z-1)/(numerator*(1+k*h))
    assert s.factor(true_derivative-complete) == 0
    assert s.factor(true_derivative.subs(h, 0)) == 0
    assert s.factor(true_derivative.subs(h, 1)) == 0
    # Removable bulk divided difference at alpha=0,1, obtained from J derivatives.
    q = 1+t
    J = s.log(1+h*(q**a-1))-a*s.log(1+t*h)
    assert s.simplify(J.subs(a, 0)) == 0
    assert s.simplify(J.subs(a, 1)) == 0
    assert s.simplify(-s.diff(J, a).subs(a, 0)-(s.log(1+t*h)-h*s.log(q))) == 0
    expected_one = h*q*s.log(q)/(1+t*h)-s.log(1+t*h)
    assert s.simplify(s.diff(J, a).subs(a, 1)-expected_one) == 0
    cases = 0
    for D in (6, 10, 18):
        families = []
        for x in (F(0), F(1, 5), F(2, 5)):
            families.append(('A', [F(1)]*(D-2)+[1-2*x, x*x]))
        for rank in range(1, D-2):
            for x in (F(0), F(1, 3), F(1)):
                families.append(('B', [1+2*x]*rank+[F(1)]*(D-rank-1)+[x*x]))
            for x in (F(1), F(3, 2), F(2), F(12, 5)):
                families.append(('C', [1+2*x]*rank+[x*x]*(D-rank-2)+[F(1)]*2))
        for name, weights in families:
            Z = sum(weights)
            values = sorted((w/Z for w in weights), reverse=True)
            assert len(values) == D and sum(values) == 1 and min(values) >= 0
            aa, cc, bb, dd = values[0], values[-3], values[-2], values[-1]
            assert aa-bb >= 0 and (aa-bb)**2 == 4*cc*dd
            assert all(x in (aa, cc) for x in values[1:-3])
            assert len(set((aa, cc, bb, dd))) <= 3
            cases += 1
    # The irrational closed endpoints are checked algebraically, not rounded inward.
    endpoint_A = s.sqrt(2)-1
    assert s.simplify(1-2*endpoint_A-endpoint_A**2) == 0
    endpoint_C = 1+s.sqrt(2)
    assert s.simplify(1+2*endpoint_C-endpoint_C**2) == 0
    # Exact lattice counterexample is useful independently of the asymptotic proof.
    q = F(5, 3)
    D = 20
    grid = max(F(D)*(D+j*(q*q-1))/(D+j*(q-1))**2 for j in range(1, D))
    assert F(16, 15)-grid == F(1, 5415)
    return {'status': 'PASS', 'sympy_version': s.__version__, 'symbolic_assertions': 12,
            'exact_qubit_conditions_cases': cases,
            'exact_rank_loss': str(F(16, 15)-grid),
            'interpretation': 'The external qubit iff APPT criterion and extreme theorem are ordinary inputs; exact list checks are finite algebra, not new proofs of those inputs.'}


def scalars():
    import mpmath as mp
    mp.mp.dps = 240

    def bulk_bar(m, a, h=None):
        t = mp.mpf(2)/(m-1)
        L = mp.log1p(t)
        if h is None:
            if a == 0:
                h = (t-L)/(t*L)
            elif a == 1:
                h = ((1+t)*L-t)/(t*t)
            else:
                b = mp.expm1(a*L)
                h = (b-a*t)/(t*(a-1)*b)
        if a == 0:
            value = mp.log1p(t*h)-h*L
        elif a == 1:
            value = h*(1+t)*L/(1+t*h)-mp.log1p(t*h)
        else:
            # Evaluate g/alpha, retaining the alpha factor for arbitrarily tiny orders.
            value = (mp.log1p(h*mp.expm1(a*L))/a-mp.log1p(t*h))/(a-1)
        return value, h

    def pole_bar(D, a):
        if a == 0:
            return mp.log1p(mp.mpf(2)/D)-mp.log(3)/D
        if a == 1:
            return -mp.log1p(mp.mpf(2)/D)+mp.mpf(3)/(D+2)*mp.log(3)
        return (mp.log1p(mp.expm1(a*mp.log(3))/D)/a-mp.log1p(mp.mpf(2)/D))/(a-1)

    orders = [mp.mpf('1e-1000'), mp.mpf('1e-30'), mp.mpf('.49'), mp.mpf('.5'),
              1-mp.mpf('1e-50'), mp.mpf(1), 1+mp.mpf('1e-50'), mp.mpf(2)]
    small = []
    for m in (25, 100, 400):
        for a in orders+[mp.sqrt(m)]:
            b, h = bulk_bar(m, a)
            assert 0 < h < 1 and b > 0
            t = mp.mpf(2)/(m-1)
            vmax = mp.mpf(1)/(m*m-1)
            r = (a+2)*t
            rho = a*abs(a-1)*vmax*mp.exp(r)/2
            assert rho < 1
            normalized = b/(vmax/2)
            assert mp.exp(-r)/(1+rho) < normalized < mp.exp(r)/(1-rho)
            small.append({'m': m, 'alpha': str(a), 'B_over_alpha_over_variance_half': mp.nstr(normalized, 30)})
    lattice = []
    pole_bounds = []
    for m in (3, 7, 25):
        for n in (100, 10000):
            D = m*n
            for a in orders+[mp.mpf(7)]:
                b, h = bulk_bar(m, a)
                nearest = {max(1, min(D-1, int(mp.floor(D*h)))), max(1, min(D-1, int(mp.ceil(D*h))))}
                grid = max(bulk_bar(m, a, mp.mpf(j)/D)[0] for j in nearest)
                scaled = (b-grid)*D*D
                assert -mp.mpf('1e-100') < scaled < 100
                lattice.append({'m': m, 'D': D, 'alpha': str(a), 'loss_D2_over_alpha': mp.nstr(scaled, 30), 'integer_ranks': sorted(nearest)})
                pb = pole_bar(D, a)
                # Interpolation at 0 and 1 bounds p_D/alpha by sup J_D''/2.
                # Every order in this loop is <=7 and D>=2; see the retained diagnosis.
                assert pb > 0 and pb*D < mp.mpf(3)**7*mp.log(3)**2
                pole_bounds.append({'m': m, 'D': D, 'alpha': str(a), 'p_D_times_D_over_alpha': mp.nstr(pb*D, 30)})
    # Full theta maximization at each selected width, not a grid in theta.
    Vrows = []
    for m in (3, 7, 25):
        D = m*10000
        t = mp.mpf(2)/(m-1)
        for a in (mp.sqrt(m)+1, mp.mpf(10), mp.mpf(1000)):
            b, _ = bulk_bar(m, a)
            Fq = mp.exp((a-1)*a*b)
            R = mp.exp(a*mp.log(mp.mpf(3*D)/(D+2)))/D
            values = []
            for k in (mp.mpf(0), t/5, t/2, t):
                eta = 2*(m-2)*k*k/(2-(m-3)*k)
                base = 1+R*((3-eta)/3)**a
                ac = mp.expm1(a*mp.log1p(k))
                h = mp.mpf(0) if k == 0 else max(mp.mpf(0), min(mp.mpf(1), (ac-a*k*base)/((a-1)*k*ac)))
                value = (base+h*ac)/(1+k*h)**a
                assert value <= (Fq+R)*(1+mp.mpf('1e-130'))
                values.append(value)
            assert max(values) >= max(Fq, 1+R)*(1-mp.mpf('1e-130'))
            Vrows.append({'m': m, 'D': D, 'alpha': mp.nstr(a, 30), 'endpoint_lower_and_all_selected_width_upper': True})
    return {'status': 'PASS', 'mpmath_version': mp.__version__, 'decimal_precision': mp.mp.dps,
            'small_width_cases': small, 'lattice_cases': lattice, 'removable_pole_cases': pole_bounds,
            'finite_V_sandwich_cases': Vrows,
            'scope': 'Finite scalar diagnostics, including alpha=1e-1000 and both sides of one. No all-state maximum or dimension threshold is inferred.'}


def wrong(name):
    import mpmath as mp
    mp.mp.dps = 180
    if name == 'v1_derivative_sign_at_theta_zero':
        actual = F(0)
        proxy = F(1)
        print(json.dumps({'variant': name, 'alpha': 2, 'kappa': 1, 'theta': 0, 'actual_derivative': str(actual), 'v1_proxy': str(proxy)}), flush=True)
        assert actual > 0, 'False: the omitted theta factor vanishes at theta=0.'
    elif name == 'omit_hole_floor':
        D = 3*10**6
        a = mp.mpf(D)**-3
        t, L = mp.mpf(1), mp.log(2)
        h = (mp.expm1(a*L)-a*t)/(t*(a-1)*mp.expm1(a*L))
        B = (mp.log1p(h*mp.expm1(a*L))-a*mp.log1p(t*h))/(a-1)
        hole = mp.log1p(mp.mpf(1)/(D-1))
        print(json.dumps({'variant': name, 'actual_APPT_witness': 'one-hole state', 'D': D, 'alpha': str(a), 'bulk_to_actual_hole_deficit': mp.nstr(B/hole, 35)}), flush=True)
        assert B/hole > mp.mpf('.9'), 'False: a bulk-only profile misses an actual hole deficit at tiny order.'
    elif name == 'replace_finite_m_bulk':
        C0 = mp.log(1/mp.log(2))-1+mp.log(2)
        relative = abs((mp.mpf(1)/18)/C0-1)
        print(json.dumps({'variant': name, 'm': 3, 'tiny_order_limit_relative_error': mp.nstr(relative, 35)}), flush=True)
        assert relative < mp.mpf('.001'), 'False: the growing-m coefficient is not the exact fixed-m tiny-order coefficient.'
    elif name in ('replace_sum_by_max', 'omit_surplus'):
        m = 400
        D = m*m
        B = mp.log1p(mp.mpf(1)/(m*m-1))
        correct = B+mp.mpf(4)/D+mp.mpf(3)/D
        bad = max(B, mp.mpf(4)/D, mp.mpf(3)/D) if name == 'replace_sum_by_max' else B+mp.mpf(4)/D
        print(json.dumps({'variant': name, 'm': m, 'D': D, 'alpha': 2, 'correct_coefficient': mp.nstr(correct*D, 35), 'wrong_coefficient': mp.nstr(bad*D, 35)}), flush=True)
        assert bad/correct > mp.mpf('.9'), 'False: the balanced first-order coefficient needs the additive head and surplus.'
    elif name == 'continuous_rank_is_exact':
        q, D = F(5, 3), 20
        grid = max(F(D)*(D+j*(q*q-1))/(D+j*(q-1))**2 for j in range(1, D))
        print(json.dumps({'variant': name, 'continuous': str(F(16, 15)), 'integer': str(grid), 'gap': str(F(16, 15)-grid)}), flush=True)
        assert grid == F(16, 15), 'False: physical integer ranks do not attain every continuous optimum exactly.'
    elif name == 'operator_convexity_substitute':
        def add(A, B): return [[A[i][j]+B[i][j] for j in range(2)] for i in range(2)]
        def scale(c, A): return [[c*A[i][j] for j in range(2)] for i in range(2)]
        def mul(A, B): return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
        def cube(A): return mul(mul(A, A), A)
        def det(A): return A[0][0]*A[1][1]-A[0][1]*A[1][0]
        A = [[F(1), F(0)], [F(0), F(1, 100)]]
        H = [[F(0), F(1)], [F(1), F(2)]]
        P = add(A, scale(F(1, 1000), H))
        Q = add(A, scale(F(-1, 1000), H))
        assert det(P) > 0 and det(Q) > 0 and P[0][0] > 0 and Q[0][0] > 0
        gap = add(scale(F(1, 2), add(cube(P), cube(Q))), scale(F(-1), cube(A)))
        assert gap[0][0]+gap[1][1] > 0
        print(json.dumps({'variant': name, 'scope': 'positive operators, not a claimed APPT-state witness', 'det_Jensen_gap': str(det(gap)), 'trace_Jensen_gap': str(gap[0][0]+gap[1][1])}), flush=True)
        assert det(gap) >= 0, 'False: scalar convex x^3 is not operator convex; its trace convexity is sufficient.'
    elif name == 'extend_C_outside_domain':
        D, j, x = 10, 2, F(3)
        values = sorted([1+2*x]*j+[x*x]*(D-j-2)+[F(1)]*2, reverse=True)
        lhs = (values[0]-values[-2])**2
        rhs = 4*values[-3]*values[-1]
        print(json.dumps({'variant': name, 'scope': 'unphysical extension outside the compact C-family parameter range', 'D': D, 'j': j, 'x': str(x), 'rank_two_lhs': str(lhs), 'rank_two_rhs': str(rhs)}), flush=True)
        assert lhs <= rhs, 'False: enlarging the C interval can violate the original qubit APPT criterion.'
    else:
        raise ValueError(name)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=('exact', 'scalars', 'wrong'))
    ap.add_argument('--name')
    args = ap.parse_args()
    if args.mode == 'exact': print(json.dumps(exact(), indent=2))
    elif args.mode == 'scalars': print(json.dumps(scalars(), indent=2))
    else: wrong(args.name)
