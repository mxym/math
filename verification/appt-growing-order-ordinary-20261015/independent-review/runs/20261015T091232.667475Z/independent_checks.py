"""Reviewer-written finite checks; no author helper or execution is reused.

The proof, not this finite collection, carries the all-state/order quantifiers.
"""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib, json, sys, traceback
from mpmath import mp

HERE = Path(__file__).resolve().parent
RUN = HERE / 'runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
(RUN / 'independent_checks.py').write_bytes(Path(__file__).read_bytes())
(RUN / 'INPUT_MANIFEST.json').write_bytes((HERE / 'INPUT_MANIFEST.json').read_bytes())
OUT = {'status': 'RUNNING', 'reviewer_written': True, 'author_code_executed': False,
       'new_Lean': False, 'full_quantified_proof': False,
       'full_quantum_optimization': False,
       'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'input_manifest_sha256': hashlib.sha256((HERE / 'INPUT_MANIFEST.json').read_bytes()).hexdigest(),
       'groups': {}, 'expected_rejections': []}

def save():
    (RUN / 'RESULT.json').write_text(json.dumps(OUT, indent=2) + '\n')

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def st(x):
    return mp.nstr(x, 32)

def deficit(alpha, histogram):
    """Exact trace-normalized histogram formula, evaluated by log-sum-exp."""
    D = sum(count for value, count in histogram)
    mean = sum(count * value for value, count in histogram) / D
    terms = [mp.log(count) + alpha * mp.log(value / mean)
             for value, count in histogram if count and value]
    high = max(terms)
    power_log = high + mp.log(sum(mp.exp(term - high) for term in terms)) - mp.log(D)
    return power_log / (alpha - 1)

def bounds(m, D, alpha):
    a = alpha - 1
    T = max(mp.log(mp.mpf(m + 1) / (m - 1)), mp.log(3) - mp.log(D) / a)
    L = mp.log(2 * alpha) / a + 4 / alpha + mp.mpf(4) / D
    U = mp.mpf(2) * m / (D - m) + 2 * mp.exp(-mp.sqrt(a)) + 2 / mp.sqrt(a) + mp.log(48) / a
    return T, L, U

def value_at(histogram, rank):
    remain = rank
    for value, count in histogram:
        if remain <= count:
            return value
        remain -= count
    raise AssertionError('Rank outside histogram')

def prefix_sum(histogram, rank, fun):
    total = mp.mpf(0); remain = rank
    for value, count in histogram:
        take = min(count, remain)
        total += take * fun(value); remain -= take
        if not remain:
            break
    need(remain == 0, 'Prefix exceeds spectrum')
    return total

def raw_physical_parameters(m, histogram):
    ordered = sorted([(mp.mpf(value), count) for value, count in histogram if count], reverse=True)
    D = sum(count for value, count in ordered)
    R, K = m * (m - 1) // 2, m * (m + 1) // 2
    b = value_at(ordered, D - K + 1)
    need(b > 0, 'Physical b must be positive even for singular state')
    scaled = [(value / b, count) for value, count in ordered]
    xR = value_at(scaled, R)
    p2 = prefix_sum(scaled, R, lambda x: (x - xR)**2)
    positive_mass = prefix_sum(scaled, R, lambda x: x - xR)
    negative_mass = prefix_sum(list(reversed(scaled)), K, lambda x: 1 - x)
    mean = sum(count * value for value, count in scaled) / D
    return scaled, b, xR - 1, p2, positive_mass + negative_mass, mean

def graph_inequality(m, weights):
    degrees = [F(0) for _ in range(m)]; index = 0
    for i in range(m):
        for j in range(i + 1, m):
            v = weights[index]; index += 1
            degrees[i] += v; degrees[j] += v
    return sum(v*v for v in weights[m-1:]), sum(d*d for d in degrees) / m

def reject(name, assertion, observations, explanation):
    item = {'variant': name, 'observations': observations, 'explanation': explanation}
    try:
        need(assertion, name)
    except AssertionError as exc:
        item.update(status='REJECTED', actual_exception=repr(exc))
    else:
        raise AssertionError('An incorrect variant passed: ' + name)
    OUT['expected_rejections'].append(item)
    (RUN / ('REJECTED-' + name + '.json')).write_text(json.dumps(item, indent=2) + '\n')

save()
try:
    graph_count = 0
    for m in range(3, 16):
        R = m * (m - 1) // 2
        lists = [[F(1, i + 1) for i in range(R)]]
        for cutoff in (0, m - 1, m, R):
            lists.append([F(int(i < cutoff)) for i in range(R)])
        for weights in lists:
            lhs, rhs = graph_inequality(m, weights)
            need(lhs <= rhs, 'Exact rational row-degree bound for decreasing weights')
            graph_count += 1
    rank_cases = 0
    for m in range(2, 10):
        R = m * (m - 1) // 2
        for n in (m, m + 1, 3*m):
            D = m*n; zeros = D - m*m
            for k in range(D + 1):
                minimum = -F(min(k, R), m)
                if k > R + zeros:
                    minimum += F(k - R - zeros, m)
                need(minimum >= -F(m-1, 2), 'All-rank negative-trace lower bound')
                need(1 + F(2, m-1)*minimum >= 0, 'All-rank projection witness positivity')
                rank_cases += 1
    OUT['groups']['exact_graph_and_rank_controls'] = {
        'rational_decreasing_row_graphs': graph_count,
        'all_integer_ranks_for_uniform_Schmidt_test': rank_cases,
        'not_exhaustive_over_all_Schmidt_vectors_or_unitaries': True}

    mp.dps = 240
    pairs = [(2,2),(2,5),(3,3),(3,11),(4,4),(7,30),(20,20),
             (1000,1000),(2,10**100),(3,10**80),(10**5,10**5),(1000,10**70)]
    rows = []; state_cases = 0; beyond = 0; m2_cases = 0
    for m, n in pairs:
        D = m*n; t = mp.mpf(2)/(m-1); q = 1+t
        orders = [mp.mpf(2),mp.mpf('2.1'),mp.mpf(4), max(mp.mpf(2),mp.mpf('.7')*mp.log(D)),
                  max(mp.mpf(2),mp.log(D)/mp.log(3)), max(mp.mpf(2),3*mp.log(D)),
                  mp.mpf(D)+1, mp.mpf(100)*D]
        for alpha in orders:
            k = max(1,int(mp.floor(mp.mpf(D)/alpha)))
            theta = mp.mpf(k)/D
            need(1 <= k < D and theta >= 1/(2*alpha), 'Finite physical rank lower bound')
            need(theta <= 1/alpha + mp.mpf(1)/D, 'Finite physical rank upper bound')
            spike = [(mp.mpf(3),1),(mp.mpf(1),D-1)]
            projection = [(q,k),(mp.mpf(1),D-k)]
            one_projection = [(q,1),(mp.mpf(1),D-1)]
            high_projection = [(q,D-1),(mp.mpf(1),1)]
            singular = [(mp.mpf(1),D-1),(mp.mpf(0),1)]
            # Convex combination of three actual APPT density matrices in one basis:
            # projection on the first k positions, spike at the last, deletion at first.
            wa, wb, wc = mp.mpf(2)/5, mp.mpf(1)/5, mp.mpf(2)/5
            na, nb, nc = D+t*k, D+2, D-1
            mix = [(wa*q/na+wb/nb,1),
                   (wa*q/na+wb/nb+wc/nc,k-1),
                   (wa/na+wb/nb+wc/nc,D-k-1),
                   (wa/na+3*wb/nb+wc/nc,1)]
            families = [spike,projection,one_projection,high_projection,singular,mix]
            T,L,U = bounds(m,D,alpha)
            values = []
            for histogram in families:
                need(sum(count for value,count in histogram)==D and
                     all(isinstance(count,int) and count>=0 for value,count in histogram),
                     'Actual nonnegative integer spectral multiplicities')
                value = deficit(alpha,histogram); values.append(value)
                need(value >= -mp.mpf('1e-150'), 'Entropy deficit of actual state nonnegative')
                need(value <= T+U+mp.mpf('1e-150'), 'Actual family below explicit upper bound')
                xs,b,kappa,p2,mass,mean = raw_physical_parameters(m,histogram)
                need(kappa >= -mp.mpf('1e-150') and kappa <= t+mp.mpf('1e-150'),
                     'All-dimensional exact physical kappa bound')
                need(p2 <= 8+mp.mpf('1e-150') and mass <= m+mp.mpf('1e-150'),
                     'All-dimensional finite head-square/mass budgets')
                need(xs[0][0] <= 3+mp.mpf('1e-150'), 'All-dimensional raw maximum bound')
                need(mean >= 1-mp.mpf(m)/D-mp.mpf('1e-150'), 'D-dependent mean bound')
                if m==2:
                    need(p2 == 0, 'm=2 has exactly p_1=0'); m2_cases += 1
                state_cases += 1
            need(max(values[:2]) >= T-L-mp.mpf('1e-150'), 'Two actual lower witnesses prove finite lower estimate')
            if alpha>D:
                need(k==1,'Actual rank remains one above dimension'); beyond+=1
            rows.append({'m':m,'n':str(n),'alpha':st(alpha),'rank':str(k),
                         'T':st(T),'L':st(L),'U':st(U),'actual_lower_witness':st(max(values[:2])),
                         'largest_checked_actual_deficit':st(max(values))})
    OUT['groups']['finite_actual_states'] = {'dimension_order_cases':len(rows),
        'state_comparisons':state_cases,'alpha_above_D_cases':beyond,
        'm2_exact_zero_head_cases':m2_cases,'rows':rows,
        'all_unitary_feasibility_from_analytic_constructions_not_numerical_sampling':True}

    # The literal original fixed-D range has an exact all-state obstruction.
    actual_spike = deficit(mp.mpf('1e6'),[(mp.mpf(3),1),(mp.mpf(1),3)])
    reject('original-fixed-D-c-infinity-corollary', mp.log(2)>=mp.log(3)-mp.mpf('.01'),
           {'m':2,'n':2,'all_order_E_upper_from_lambda_max_le_half':st(mp.log(2)),
            'attaining_spike_deficit_at_order_1e6':st(actual_spike),'original_claimed_limit':st(mp.log(3))},
           'Maximally entangled two-qubit witness forces lambda_1<=1/2; the spike attains it at infinite order.')
    raw = mp.log(mp.mpf(3)/4)/6
    correct = deficit(mp.mpf(7),[(mp.mpf(1),3),(mp.mpf(0),1)])
    reject('omit-exact-mean-normalization', abs(raw-correct)<mp.mpf('.001'),
           {'raw_power_score':st(raw),'correct_singular_APPT_deficit':st(correct)},
           'Dropping the trace mean even gives a negative score for this actual singular APPT state.')
    m,D,alpha = 3,3*10**250,mp.mpf(50)
    k = max(1,int(mp.floor(mp.mpf(D)/alpha)))
    actual = deficit(alpha,[(mp.mpf(2),k),(mp.mpf(1),D-k)])
    false = max(mp.mpf(0),mp.log(3)-mp.log(D)/(alpha-1))
    reject('drop-fixed-m-log-q-branch', actual<=false+mp.mpf('.01'),
           {'actual_projection_deficit':st(actual),'false_spike_only_formula':st(false)},
           'A fixed-m bulk plateau persists when the logarithmic spike branch is below zero.')
    D,alpha = 100,mp.mpf(10000)
    fractional = mp.mpf(D)/alpha
    reject('fractional-rank-below-one', fractional>=1 and mp.floor(fractional)==fractional,
           {'D':D,'alpha':st(alpha),'unphysical_fractional_rank':st(fractional),'physical_rank':1},
           'A positive fractional multiplicity below one is not a finite density-matrix rank.')
    # Existing exact finite purity input F16 bounds ALL actual states, not a chosen family.
    D=2*10**12
    purity_deficit_upper=mp.log(mp.mpf(4)*D/(3*(D-2))+mp.mpf(18)*D/(D-2)**2)
    reject('fixed-m-c-zero-with-bounded-order', purity_deficit_upper>=mp.log(3)-mp.mpf('.01'),
           {'m':2,'alpha':2,'D':D,'all_APPT_deficit_upper_from_F16':st(purity_deficit_upper),
            'incorrect_bulk_endpoint_claim':st(mp.log(3))},
           'Fixed-m c=0 requires alpha->infinity; at bounded order two the whole-set purity bound stays near log(4/3).')
    weights=[F(0)]*5+[F(1)]
    lhs,rhs=graph_inequality(4,weights)
    reject('row-degree-bound-without-decreasing-order', lhs<=rhs,
           {'m':4,'tail_square_sum':str(lhs),'degree_square_mean':str(rhs)},
           'The graph input uses decreasing paired gaps. Removing that hypothesis is false.')
    OUT['status']='PASS'
except BaseException as exc:
    OUT.update(status='FAIL',error=str(exc),traceback=traceback.format_exc())
    print(OUT['traceback'],flush=True)
finally:
    save()
    print(json.dumps({'status':OUT['status'],'run':str(RUN),
                      'expected_rejections':len(OUT['expected_rejections']),
                      'full_quantified_proof':False}),flush=True)
if OUT['status']!='PASS':
    sys.exit(1)
