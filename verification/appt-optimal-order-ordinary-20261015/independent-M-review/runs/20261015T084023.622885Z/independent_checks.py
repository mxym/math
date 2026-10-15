"""Independent finite diagnostics and deliberately rejected M proof variants.

Written by the reviewer agent. No author functions are imported, AST-selected,
executed or copied here. These finite calculations are not quantified proofs.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, sys, traceback
from mpmath import mp
import sympy as sp

HERE = Path(__file__).resolve().parent
RUN = HERE / 'runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
(RUN / 'independent_checks.py').write_bytes(Path(__file__).read_bytes())
MANIFEST = json.loads((HERE / 'INPUT_MANIFEST.json').read_text())
(RUN / 'INPUT_MANIFEST.json').write_bytes((HERE / 'INPUT_MANIFEST.json').read_bytes())
OUT = {'status': 'RUNNING', 'reviewer_agent_written': True,
       'author_script_executed': False, 'new_Lean': False,
       'full_quantified_proof': False, 'full_quantum_optimization': False,
       'input_manifest_sha256': hashlib.sha256((HERE / 'INPUT_MANIFEST.json').read_bytes()).hexdigest(),
       'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'groups': {}, 'expected_rejections': []}

def save():
    (RUN / 'RESULT.json').write_text(json.dumps(OUT, indent=2) + '\n')

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def scalar(x):
    return mp.nstr(x, 38)

def exp_ratio(x):
    return mp.expm1(x) / x if x else mp.mpf(1)

def log_ratio(x):
    return mp.log1p(x) / x if x else mp.mpf(1)

def phi(a, y):
    """psi_a(y)/a, regular at a=0; all uses here stay away from a=1."""
    L = mp.log(y)
    return (L * exp_ratio(a * L) - (y - 1)) / (a - 1)

def normalized_deficit_over_order(a, histogram):
    """Factored formula prevents loss of the arbitrarily tiny order."""
    D = sum(count for raw, count in histogram)
    average = sum(count * raw for raw, count in histogram) / D
    A0 = sum(count * phi(a, raw / average) for raw, count in histogram) / D
    return A0 * log_ratio((a - 1) * a * A0)

def deficit(a, histogram):
    """Independent log-sum-exp evaluation, robust for enormous orders."""
    D = sum(count for raw, count in histogram)
    S = sum(count * raw for raw, count in histogram)
    logs = [mp.log(count) + a * mp.log(raw) for raw, count in histogram if count]
    top = max(logs)
    L = top + mp.log(sum(mp.exp(v - top) for v in logs))
    return (L - mp.log(D) - a * mp.log(S / D)) / (a - 1)

def bulk_continuous_rank(a, D, r):
    L = mp.log1p(r)
    Q0 = L * exp_ratio(a * L)
    return D * (Q0 - r) / ((a - 1) * r * Q0)

def body_histogram(D, r, k):
    return [(1 + r, k), (mp.mpf(1), D - k)]

def adjacent(x):
    return sorted({int(mp.floor(x)), int(mp.ceil(x))})

def negative_histogram(D, r, beta, k):
    return [(1 + r, k), (1 - beta, 1), (mp.mpf(1), D - k - 1)]

def positive_histogram(D, r, p, k):
    return [(1 + r + p, 1), (1 + r, k - 1), (mp.mpf(1), D - k)]

def exact_body_derivative(a, theta, r):
    return (a * theta * (1 - theta) * mp.expm1((a - 1) * mp.log1p(r)) /
            ((a - 1) * (1 + theta * mp.expm1(a * mp.log1p(r))) * (1 + theta * r)))

def expected_rejection(name, assertion, observed, explanation):
    record = {'variant': name, 'observed': observed, 'explanation': explanation}
    try:
        need(assertion, name)
    except AssertionError as exc:
        record.update(status='REJECTED', actual_exception=repr(exc))
    else:
        raise AssertionError('Negative control was not rejected: ' + name)
    OUT['expected_rejections'].append(record)
    (RUN / ('REJECTED-' + name + '.json')).write_text(json.dumps(record, indent=2) + '\n')

save()
try:
    # Pure algebra: replace the two powers by formal independent symbols.
    a, th, r, X, Y = sp.symbols('a th r X Y')
    A = 1 + th * (X - 1)
    raw = a * th / (a - 1) * (Y / A - 1 / (1 + th * r))
    factored = a * th * (1 - th) * (Y - 1) / ((a - 1) * A * (1 + th * r))
    need(sp.simplify((raw - factored).subs(X, (1 + r) * Y)) == 0,
         'Exact body derivative factorization')
    xx, h, z, g, D = sp.symbols('x h z g D')
    need(sp.expand((2**2 - 1 - 2) - 2**(2 - 2)) == 0,
         'Kernel-gap equality at order two')
    need(sp.simplify((2 / (xx - 1))**2 - (2 / (xx + 1))**2 - 16 * xx / (xx**2 - 1)**2) == 0,
         'Exact contrast-square difference')
    need(sp.simplify(sp.diff(-sp.log(1 - g / (xx * D)), D) + g / (D**2 * xx * (1 - g / (xx * D)))) == 0,
         'Exact dimension derivative of head logarithm')
    OUT['groups']['symbolic'] = {'checks': 4, 'result': 'PASS'}

    mp.dps = 220
    def psi(aa, yy):
        return aa * phi(aa, yy)
    def psi_y(aa, yy):
        return aa * mp.log(yy) * exp_ratio((aa - 1) * mp.log(yy))
    def equations(aa, p, beta):
        fp = psi(aa, 1 + p)
        fm = psi(aa, 1 - beta)
        return (p * (2 - p) * psi_y(aa, 1 + p) - 2 * fp,
                beta * (1 - beta) * (-psi_y(aa, 1 - beta)) - fm,
                (2 - p) * fp / (2 * aa * p) - (1 - beta) * fm / (aa * beta))
    ax, p0, beta0 = mp.findroot(equations, (mp.mpf('.55'), mp.mpf('.85'), mp.mpf('.61')))
    d0 = (2 - p0) * psi(ax, 1 + p0) / (2 * ax * p0)
    old_result = HERE / 'snapshot' / 'L-review' / 'independent-RESULT.json'
    old_data = json.loads(old_result.read_text())
    ac = mp.mpf(old_data['groups']['independently_evaluated_constants']['ac_illustration'])
    (RUN / 'previous-independent-L-RESULT.json').write_bytes(old_result.read_bytes())
    B = abs(ac) + 2
    OUT['groups']['constants'] = {
        'independently_resolved_alpha0': scalar(ax), 'independently_resolved_d0': scalar(d0),
        'ac_from_previous_independent_L_diagnostic': scalar(ac),
        'previous_result_sha256': hashlib.sha256(old_result.read_bytes()).hexdigest(),
        'numeric_illustrations_not_intervals': True}

    tiny_rows, growth_rows, derivative_rows, enormous_rows = [], [], [], []
    zminus = (1 + mp.sqrt(5)) / 2
    for m in (3000, 12000, 48000):
        n = int(mp.floor(d0 * m * m + B * m)); D = m * n
        t = mp.mpf(2) / (m - 1)
        # All these computations first divide by order, including its zero limit.
        for aa in map(mp.mpf, ('0', '.5', '.31', '1e-80', '1e-500')):
            rr = mp.mpf(2) / (m - 1 + zminus)
            beta = (2 + rr) * zminus / (2 * (1 + zminus))
            Q0 = mp.log1p(rr) * exp_ratio(aa * mp.log1p(rr))
            H0 = mp.log1p(-beta) * exp_ratio(aa * mp.log1p(-beta))
            kh = (Q0 * (D - beta) - rr * (D + aa * H0)) / ((aa - 1) * rr * Q0)
            ks = adjacent(kh)
            need(all(m * (m - 1) // 2 <= k <= D - m * (m + 1) // 2 for k in ks),
                 'Tiny-order actual physical integer rank')
            head = max(normalized_deficit_over_order(aa, negative_histogram(D, rr, beta, k)) for k in ks)
            bk = adjacent(bulk_continuous_rank(aa, D, t))
            bulk = max(normalized_deficit_over_order(aa, body_histogram(D, t, k)) for k in bk)
            gain = D * (head - bulk)
            need(gain > 0, 'Factored tiny-order actual witness')
            real_head = normalized_deficit_over_order(aa, negative_histogram(D, rr, beta, kh))
            loss = real_head - head
            need(loss >= -mp.mpf('1e-180') and abs(loss) * m**8 < 2 / d0**2,
                 'Tiny-order factored physical-rank loss')
            tiny_rows.append({'m': m, 'alpha': scalar(aa), 'D_gain_divided_by_alpha': scalar(gain),
                              'm8_rank_loss_divided_by_alpha': scalar(loss * m**8),
                              'zero_is_analytic_limit_not_positive_order': not bool(aa)})
        star = mp.mpf(5) * mp.log(m) / (2 * mp.log(2))
        rr = mp.mpf(2) / (m + 1); p = 1 + rr / 2
        for aa in [mp.mpf(2), mp.mpf('2.001'), mp.sqrt(star), star * mp.mpf('.73'), star]:
            k = max(adjacent(bulk_continuous_rank(aa, D, t)),
                    key=lambda j: deficit(aa, body_histogram(D, t, j)))
            need(m * (m - 1) // 2 <= k <= D - m * (m + 1) // 2,
                 'Growing-order exact integer bulk winner is physical')
            th = mp.mpf(k) / D
            head = deficit(aa, positive_histogram(D, rr, p, k))
            mid = deficit(aa, body_histogram(D, rr, k))
            bulk = deficit(aa, body_histogram(D, t, k))
            kernel = (mp.power(2, aa) - 1 - aa) / (aa - 1)
            rel = D * (head - mid) / kernel
            err = aa / m + 1 / mp.sqrt(m)
            need(abs(rel - 1) < 8 * err, 'Uniform relative growing-order head estimate')
            cost = D * (bulk - mid) / aa
            need(cost < 2 * mp.mpf(D) / m**3 * (1 + 4 * aa / m),
                 'Uniform relative growing-order body penalty')
            need(head > bulk, 'Growing-order strict actual witness')
            growth_rows.append({'m': m, 'alpha': scalar(aa), 'relative_head_gain': scalar(rel),
                                'D_body_loss_over_alpha': scalar(cost),
                                'D_net_gain_over_alpha': scalar(D * (head - bulk) / aa)})
            for x in (rr, (rr + t) / 2, t):
                exact = exact_body_derivative(aa, th, x)
                num = mp.diff(lambda v: deficit(aa, body_histogram(D, v, k)), x)
                need(abs(exact - num) < mp.mpf('1e-180'), 'Exact derivative versus differentiated entropy')
                scale = exact / (aa * th * (1 - th) * x)
                need(abs(scale - 1) < 3 * aa * x, 'Derivative growing-order relative error')
                derivative_rows.append({'m': m, 'alpha': scalar(aa),
                                        'scaled_relative_error': scalar(abs(scale - 1) / (aa * x))})
        # Fix the STATE at star. None of its entries, rank or normalization change below.
        kstar = max(adjacent(bulk_continuous_rank(star, D, t)),
                    key=lambda j: deficit(star, body_histogram(D, t, j)))
        fixed_hist = positive_histogram(D, rr, p, kstar)
        upper = mp.log1p(t); previous = None
        for aa in (star, star + mp.mpf('.01'), 3 * star, mp.mpf('1e7'), mp.mpf('1e30')):
            val = deficit(aa, fixed_hist)
            need(val > upper, 'One fixed actual state beats all-order bulk upper bound')
            if previous is not None:
                need(val >= previous, 'Same fixed state has monotone entropy deficit')
            previous = val
            enormous_rows.append({'m': m, 'alpha': scalar(aa), 'state_deficit': scalar(val),
                                  'universal_bulk_upper_bound': scalar(upper),
                                  'fixed_rank': kstar})

    OUT['groups']['tiny_order_factorization'] = {'cases': len(tiny_rows), 'rows': tiny_rows,
        'smallest_positive_order': '1e-500', 'analytic_zero_limit_included': True,
        'unfactored_arbitrary_tiny_subtraction_avoided': True}
    OUT['groups']['growing_order_gain'] = {'cases': len(growth_rows), 'rows': growth_rows}
    OUT['groups']['exact_derivative'] = {'cases': len(derivative_rows), 'rows': derivative_rows}
    OUT['groups']['fixed_state_unbounded_samples'] = {'cases': len(enormous_rows), 'rows': enormous_rows,
        'largest_sample_order': '1e30', 'not_a_proof_of_the_unbounded_quantifier': True}

    # Adversarial controls are actual rejected assertions, retained as separate JSONs.
    m = 48000; n = int(mp.floor(d0 * m * m + B * m)); D = m * n
    t = mp.mpf(2) / (m - 1); rr = mp.mpf(2) / (m + 1); p = 1 + rr / 2
    aa = mp.mpf(2)
    k = max(adjacent(bulk_continuous_rank(aa, D, t)),
            key=lambda j: deficit(aa, body_histogram(D, t, j)))
    h0 = deficit(aa, positive_histogram(D, rr, p, k))
    b0 = deficit(aa, body_histogram(D, rr, k))
    observed = D * (h0 - b0)
    expected_rejection('omit-head-trace-normalization', abs(observed - 3) < mp.mpf('.01'),
        {'true_D_gain_at_alpha2': scalar(observed), 'incorrect_power_only_limit': '3',
         'true_kernel_limit': '1'}, 'Dropping the trace logarithm changes the leading kernel by two.')

    badstar = 2 * mp.log(m) / mp.log(2)
    kb = max(adjacent(bulk_continuous_rank(badstar, D, t)),
             key=lambda j: deficit(badstar, body_histogram(D, t, j)))
    bad_value = deficit(badstar, positive_histogram(D, rr, p, kb))
    expected_rejection('cutoff-exponent-two-for-monotonicity', bad_value > mp.log1p(t),
        {'actual_state_deficit': scalar(bad_value), 'bulk_universal_upper': scalar(mp.log1p(t)),
         'incorrect_cutoff': scalar(badstar)},
        'At exponent two this proposed monotonicity bridge does not reach the universal bulk upper bound.')

    order = mp.mpf('1e-500')
    positive_leading_scale = order / m**3
    absolute_rank_error_bound = mp.mpf(1) / m**8
    expected_rejection('absolute-instead-of-alpha-relative-rank-error',
        positive_leading_scale > absolute_rank_error_bound,
        {'order_times_m_minus3': scalar(positive_leading_scale),
         'unfactored_m_minus8_error': scalar(absolute_rank_error_bound)},
        'An absolute error, even m^-8, cannot establish strict improvement for arbitrarily tiny positive order.')
    OUT['status'] = 'PASS'
except BaseException as exc:
    OUT.update(status='FAIL', error=str(exc), traceback=traceback.format_exc())
    print(OUT['traceback'], flush=True)
finally:
    save()
    print(json.dumps({'status': OUT['status'], 'run': str(RUN),
                      'expected_rejections': len(OUT['expected_rejections']),
                      'full_quantified_proof': False}), flush=True)
if OUT['status'] != 'PASS':
    sys.exit(1)
