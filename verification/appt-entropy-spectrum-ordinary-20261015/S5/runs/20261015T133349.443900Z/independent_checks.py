"""New reviewer-written controls; no author imports, generated code, or AST reuse.

Finite controls supplement the analytic review. They do not establish the
all-matrix or all-sequence assertions by sampling. The matrix witnesses used
here have the all-unitary positivity proofs stated in the reviewed sources.
"""
from fractions import Fraction as F
from math import isqrt
import argparse
import json
import platform


def frac(x):
    return F(x)


def compressed(m, n, raw_levels):
    """Normalize raw positive/zero eigenvalues with their physical integer counts."""
    D = m*n
    merged = {}
    for value, count in raw_levels:
        assert isinstance(count, int) and count >= 0
        value = F(value)
        assert value >= 0
        if count:
            merged[value] = merged.get(value, 0) + count
    assert sum(merged.values()) == D
    trace = sum(value*count for value, count in merged.items())
    assert trace > 0
    levels = sorted(((D*value/trace, count) for value, count in merged.items()), reverse=True)
    assert sum(value*count for value, count in levels) == D
    R, K = m*(m-1)//2, m*(m+1)//2
    j = D-K+1
    body = []
    start = 1
    for value, count in levels:
        overlap = max(0, min(start+count-1, j)-max(start, R)+1)
        if overlap:
            body.append((value, overlap))
        start += count
    N = sum(count for _, count in body)
    assert N == D-m*m+2 > 0
    A = body[-1][0]
    assert A > 0
    kap = body[0][0]/A-1
    L = (m-1)*kap
    mu = sum(value*count for value, count in body)/N
    theta = (mu/A-1)/kap if kap else F(0)
    J = sum(count*((m-1)*(value/A-1))*(L-(m-1)*(value/A-1)) for value, count in body)/N
    Q = sum(count*(value-1)**2 for value, count in levels)
    QB = sum(count*(value-1)**2 for value, count in body)
    mean_part = F(m*m*N, D)*(mu-1)**2
    variance_part = F(N, D)*F(m, m-1)**2*A*A*(L*L*theta*(1-theta)-J)
    assert QB/F(n, m) == variance_part+mean_part
    # Exact one-dimensional quantile transport to beta, without constructing D atoms.
    beta_left = F(1, 2)
    W2sq = F(0)
    for y, count in reversed(levels):
        mass = F(count, D)
        to_left = min(mass, beta_left)
        x = m*(y-1)
        W2sq += to_left*(x+1)**2 + (mass-to_left)*(x-1)**2
        beta_left -= to_left
    assert beta_left == 0
    return {'m': m, 'n': n, 'D': D, 'levels': levels, 'body': body,
            'N': N, 'A': A, 'kappa': kap, 'L': L, 'theta': theta, 'J': J,
            'mu': mu, 'Q': Q, 'QB': QB, 'QE': Q-QB,
            'mean_part': mean_part, 'variance_part': variance_part, 'W2sq': W2sq}


def exact_moment(state, alpha):
    assert isinstance(alpha, int) and alpha >= 2
    D = state['D']
    result = sum(count*value**alpha for value, count in state['levels'])/D
    kernel = sum(count*(value**alpha-1-alpha*(value-1)) for value, count in state['levels'])
    assert D*(result-1) == kernel
    a = F(alpha*(alpha-1), 2)
    # Independent pointwise Taylor envelope on the actual middle interval.
    delta = max(abs(value-1) for value, _ in state['body'])
    assert delta < 1
    midkernel = sum(count*(value**alpha-1-alpha*(value-1)) for value, count in state['body'])
    assert a*state['QB']*(1-delta)**(alpha-2) <= midkernel <= a*state['QB']*(1+delta)**(alpha-2)
    U = F(3*D, D+2)**alpha
    V = a*F(state['n'], state['m'])
    return {'M': result, 'U': U, 'V': V, 'wp': U/(U+V),
            'ratio_G1_equivalent': D*(result-1)/(U+V),
            'state_uniform_identity_error': (D*(result-1)-state['levels'][0][0]**alpha-a*state['Q'])/(U+V)}


def pole(m, n, strength=F(2)):
    return compressed(m, n, [(1+strength, 1), (F(1), m*n-1)])


def three_level(alpha):
    m = alpha*alpha
    n = m*3**(2*alpha)
    D = m*n
    assert D % 4 == 0
    t = F(2, m-1)
    return compressed(m, n, [(1+t, D//4), (1+t/2, D//2), (F(1), D//4)])


def protected(m, n, alpha):
    H = isqrt(alpha*m)
    H += H*H < alpha*m
    kappa = F(2, m+H)
    q = 2-(m-3)*kappa
    eta = 2*(m-2)*kappa*kappa/q
    d = 2-kappa-eta
    assert q > 0 and d >= 0
    assert d*q == (2-(m-1)*kappa)*(2+kappa)
    k = -(-((m-1)*n)//2)
    assert 1 <= k < m*n
    return compressed(m, n, [(3-eta, 1), (1+kappa, k-1), (F(1), m*n-k)])


def brief(state, moment=None):
    row = {k: str(state[k]) for k in ('m', 'n', 'D', 'N', 'L', 'theta', 'J', 'mu', 'Q', 'QE', 'W2sq', 'mean_part')}
    if moment:
        row.update({k: str(moment[k]) for k in ('wp', 'ratio_G1_equivalent', 'state_uniform_identity_error')})
    return row


def symbolic_and_exact():
    import sympy as s
    m, A, L, th, J = s.symbols('m A L theta J', real=True)
    mean = A*(1+L*th/(m-1))
    direct = (A-1)**2 + 2*(A-1)*A*L*th/(m-1) + A*A*(L*L*th-J)/(m-1)**2
    centered = A*A*(L*L*th*(1-th)-J)/(m-1)**2+(mean-1)**2
    assert s.factor(direct-centered) == 0
    delta = s.symbols('delta', real=True)
    kap = (2-delta)/(m-1)
    eta = 2*(m-2)*kap**2/(2-(m-3)*kap)
    assert s.factor(eta-2*(m-2)*(2-delta)**2/((m-1)*(4+(m-3)*delta))) == 0
    # Re-derive the actual protected-spike sufficient quadratic from pair sums.
    c, x, y, T, Q = s.symbols('c x y T Q', real=True)
    r = m-2
    q = 2-(m-3)*c
    d = 2-c-2*r*c*c/q
    R0 = q/(2*r)
    original = x*x+y*y+Q-c*(x*y+(x+y)*T+(T*T-Q)/2)-d*x*y
    sos = (2+c+d)*(x-y)**2/4+(1+c/2)*(Q-T*T/r)+R0*(T-c*(x+y)/(2*R0))**2
    assert s.factor(original-sos) == 0
    # Nonnegative body loss separates all three variables with no cancellation.
    assert s.expand(1-(L*L*th*(1-th)-J) - (1-L*L/4+L*L*(th-s.Rational(1, 2))**2+J)) == 0
    rows = []
    for alpha in (4, 8, 12, 20):
        mm = alpha*alpha
        balanced_n = -(-(2*mm*3**alpha)//(alpha*(alpha-1)))
        specimens = [('identity', compressed(mm, mm, [(F(1), mm*mm)])),
                     ('singular_one_hole', compressed(mm, mm, [(F(1), mm*mm-1), (F(0), 1)])),
                     ('balanced_pole', pole(mm, balanced_n)),
                     ('square_pole', pole(mm, mm)),
                     ('three_level_J', three_level(alpha))]
        specimens += [('protected_'+label, protected(mm, nn, alpha)) for label, nn in
                      [('square', mm), ('balanced', balanced_n), ('escaping_aspect', mm*3**(2*alpha))]]
        for name, state in specimens:
            moment = exact_moment(state, alpha)
            assert 0 <= state['kappa'] <= F(2, mm-1)
            assert 0 <= state['theta'] <= 1 and state['J'] >= 0
            assert state['levels'][0][0] <= F(3*state['D'], state['D']+2)
            rows.append({'case': name, 'alpha': alpha, **brief(state, moment)})
        body = specimens[4][1]
        assert body['Q']/F(body['n'], mm) == F(1, 2)
        assert body['mu']-1 == F(1, body['N'])
        assert body['mean_part'] > 0
        assert body['L'] == 2
        assert F(49, 100) < exact_moment(body, alpha)['ratio_G1_equivalent'] < F(3, 5)
        bp = specimens[2][1]
        assert bp['L'] == bp['J'] == 0 and bp['theta'] == 0
        assert F(2, 5) < exact_moment(bp, alpha)['ratio_G1_equivalent'] < F(3, 5)
    return {'status': 'PASS', 'symbolic_identites': 4, 'exact_compressed_actual_state_cases': len(rows),
            'rows': rows, 'sympy_version': s.__version__, 'python': platform.python_version(),
            'limits': 'Finite exact identities/regressions; all-global-unitary positivity and infinite limits are analytic, not established by these samples.'}


def mp_value(x, mp):
    if isinstance(x, F):
        return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)


def real_order():
    import mpmath as mp
    mp.mp.dps = 180
    rows = []
    # Real, nonintegral orders check the integral-kernel envelope without integer-power restriction.
    for m, n in ((37, 41), (101, 100003), (1009, 10**70+3)):
        for alpha in (mp.mpf('2.125'), mp.mpf('3.7'), mp.mpf('11.25')):
            state = protected(m, n, 7)
            values = [(mp_value(y, mp), count) for y, count in state['levels']]
            body = [(mp_value(y, mp), count) for y, count in state['body']]
            D = state['D']
            M = sum(count*y**alpha for y, count in values)/D
            kernel = sum(count*(y**alpha-1-alpha*(y-1)) for y, count in values)
            assert mp.almosteq(D*(M-1), kernel, rel_eps=mp.mpf('1e-100'), abs_eps=mp.mpf('1e-100'))
            delta = max(abs(y-1) for y, _ in body)
            a = alpha*(alpha-1)/2
            QB = mp_value(state['QB'], mp)
            midkernel = sum(count*(y**alpha-1-alpha*(y-1)) for y, count in body)
            assert a*QB*(1-delta)**(alpha-2) <= midkernel <= a*QB*(1+delta)**(alpha-2)
            rows.append({'case': 'real_order_centered_kernel', 'm': m, 'n': str(n), 'alpha': str(alpha), 'checked': True})
    # Actual reduced-strength poles: entropy/moment separation at the paper's sublinear scale.
    separated = []
    for alpha in (64, 256, 1024):
        m = alpha*alpha
        D = m*m
        strength = 2-1/mp.sqrt(alpha)
        y = D*(1+strength)/(D+strength)
        tail = D/(D+strength)
        u = mp.mpf(3*D)/(D+2)
        U = u**alpha
        V = mp.mpf(alpha*(alpha-1))/2
        M = (y**alpha+(D-1)*tail**alpha)/D
        h = alpha*mp.log(u/y)
        chi = mp.log(U/D)
        ratio = D*(M-1)/(U+V)
        ent = mp.log(M)/mp.log1p((U+V)/D)
        assert h > 0 and chi > 0 and 0 < ratio < ent < 1
        separated.append({'alpha': alpha, 'h': mp.nstr(h, 35), 'h_over_chi': mp.nstr(h/chi, 35),
                          'moment_excess_ratio_G1': mp.nstr(ratio, 35), 'entropy_ratio_G1': mp.nstr(ent, 35)})
    assert mp.mpf(separated[-1]['moment_excess_ratio_G1']) < mp.mpf('0.0001')
    assert mp.mpf(separated[-1]['entropy_ratio_G1']) > mp.mpf('0.98')
    # A state-relative log error is controlled by its error relative to 1+actual peak.
    scalar = []
    for chi in (mp.mpf(20), mp.mpf(200), mp.mpf(1000)):
        for h in (mp.mpf(0), chi/2, chi, 2*chi):
            peak = mp.exp(chi-h)
            eps = mp.mpf('1e-20')
            rem = mp.mpf('1e-30')
            actual = 1+(1-eps)*peak+rem
            log_error = abs(mp.log(actual)-mp.log1p(peak))
            bound = 2*(eps+rem)
            assert log_error < bound
            scalar.append({'chi': str(chi), 'h': str(h), 'log_error': mp.nstr(log_error, 20), 'bound': str(bound)})
    return {'status': 'PASS', 'mpmath': mp.__version__, 'decimal_precision': mp.mp.dps,
            'real_order_cases': rows, 'actual_pole_separation': separated, 'state_relative_scalar_cases': scalar,
            'limits': 'Finite high-precision diagnostics only; they do not prove either all-state asymptotic implication.'}


def wrong_variant(name):
    """Each selected false mathematical assertion must really raise AssertionError."""
    a = 20
    m = a*a
    if name == 'branch_minimum':
        n = -(-(2*m*3**a)//(a*(a-1)))
        state = pole(m, n)
        moment = exact_moment(state, a)
        print(json.dumps({'variant': name, 'actual_physical_witness': 'pure pole', **brief(state, moment)}, indent=2), flush=True)
        assert moment['ratio_G1_equivalent'] > F(9, 10), 'False: zero peak defect alone does not saturate the weighted sum.'
    elif name == 'omit_J':
        state = three_level(a)
        moment = exact_moment(state, a)
        assert state['L'] == 2 and abs(state['theta']-F(1, 2)) < F(1, 10**10)
        print(json.dumps({'variant': name, 'actual_physical_witness': 'operator-interval three-level state', **brief(state, moment)}, indent=2), flush=True)
        assert state['Q']/F(state['n'], m) > F(9, 10), 'False: width and mean do not remove the positive J loss.'
    elif name == 'omit_mean_square':
        state = three_level(8)
        print(json.dumps({'variant': name, 'actual_physical_witness': 'operator-interval three-level state', **brief(state)}, indent=2), flush=True)
        assert state['QB']/F(state['n'], state['m']) == state['variance_part'], 'False: actual middle mean is not exactly one.'
    elif name == 'unweighted_W2':
        state = pole(m, m)
        moment = exact_moment(state, a)
        assert moment['ratio_G1_equivalent'] > F(99, 100)
        print(json.dumps({'variant': name, 'actual_physical_witness': 'square pure pole', **brief(state, moment)}, indent=2), flush=True)
        assert state['W2sq'] < F(1, 100), 'False: a negligible bulk weight does not require the full beta W2 law.'
    elif name == 'entropy_requires_moment':
        import mpmath as mp
        mp.mp.dps = 150
        a = 1024
        m = a*a
        D = m*m
        b = 2-1/mp.sqrt(a)
        M = ((D*(1+b)/(D+b))**a+(D-1)*(D/(D+b))**a)/D
        U = (mp.mpf(3*D)/(D+2))**a
        V = mp.mpf(a*(a-1))/2
        moment = D*(M-1)/(U+V)
        entropy = mp.log(M)/mp.log1p((U+V)/D)
        print(json.dumps({'variant': name, 'actual_physical_witness': 'reduced-strength square pole', 'alpha': a,
                          'moment_ratio': mp.nstr(moment, 35), 'entropy_ratio': mp.nstr(entropy, 35)}, indent=2), flush=True)
        assert entropy > mp.mpf('.98')
        assert moment > mp.mpf('.9'), 'False: relative entropy tolerates h=o(chi), unlike moment excess.'
    elif name == 'log_coarse_error':
        import mpmath as mp
        mp.mp.dps = 150
        chi = mp.mpf(200)
        actual = 1+mp.exp(chi/2)
        optimum_scale = mp.exp(chi)
        coarse_error = mp.exp(3*chi/4)
        assert coarse_error/optimum_scale < mp.mpf('1e-20')
        print(json.dumps({'variant': name, 'scope': 'scalar proof-method countercontrol, not an asserted new quantum witness',
                          'chi': str(chi), 'relative_to_optimum_scale_error': mp.nstr(coarse_error/optimum_scale, 35),
                          'true_log': mp.nstr(mp.log(actual), 35), 'perturbed_log': mp.nstr(mp.log(actual+coarse_error), 35)}, indent=2), flush=True)
        assert abs(mp.log(actual+coarse_error)-mp.log(actual)) < 1, 'False: o(optimum peak) error need not be small after logging a much smaller actual moment.'
    else:
        raise ValueError(name)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=('exact', 'real', 'variant'))
    ap.add_argument('--name')
    args = ap.parse_args()
    if args.mode == 'exact':
        print(json.dumps(symbolic_and_exact(), indent=2))
    elif args.mode == 'real':
        print(json.dumps(real_order(), indent=2))
    else:
        wrong_variant(args.name)
