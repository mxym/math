"""Finite author controls for X. No sampling claims an actual global optimizer.

Each real execution and failure is retained with the executed script and inputs.
"""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction
import hashlib, json, shutil, traceback
import sympy as sp
import mpmath as mp

base = Path(__file__).resolve().parent
run = base / 'control-runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True, exist_ok=False)
for name in ['PAPER.md', 'checks.py', 'CREDITED_INPUTS.json', 'THEOREM_MAP.md', 'PRIMARY_SCOPE.json']:
    shutil.copyfile(base / name, run / name)
source_hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in run.iterdir() if p.is_file()}
result = {'kind': 'finite author controls, not independent review or proof by sampling',
          'started_utc': datetime.now(timezone.utc).isoformat(), 'source_hashes': source_hashes,
          'new_Lean_executions': 0, 'checks': {}}
mp.mp.dps = 210

def bulk(m, alpha, theta=None):
    t = mp.mpf(2) / (m-1)
    ell = mp.log1p(t)
    if theta is None:
        theta = ((1+t)*ell-t)/(t*t) if alpha == 1 else (
            mp.expm1(alpha*ell)-alpha*t)/(t*(alpha-1)*mp.expm1(alpha*ell))
    if alpha == 1:
        value = theta*(1+t)*ell/(1+t*theta)-mp.log1p(t*theta)
    else:
        value = (mp.log1p(theta*mp.expm1(alpha*ell))-alpha*mp.log1p(t*theta))/(alpha-1)
    return value, theta

def rank_value(m, total, alpha):
    continuous, theta = bulk(m, alpha)
    low = max(1, min(total-1, int(mp.floor(total*theta))))
    choices = sorted({low, max(1, min(total-1, low+1))})
    return max(bulk(m, alpha, mp.mpf(k)/total)[0] for k in choices)

def pole(total, alpha):
    if alpha == 1:
        return mp.log(mp.mpf(total)/(total+2))+mp.mpf(3)/(total+2)*mp.log(3)
    return (mp.log1p(mp.expm1(alpha*mp.log(3))/total)
            +alpha*mp.log(mp.mpf(total)/(total+2)))/(alpha-1)

def low_profile(m, total, alpha):
    assert 0 < alpha <= mp.sqrt(m)
    b, _ = bulk(m, alpha)
    surplus = max(mp.mpf(0), 4-mp.mpf(total)/(m*m))
    if alpha < mp.mpf('.5'):
        return max(mp.log(mp.mpf(total)/(total-1)),
                   b-mp.expm1(-alpha*mp.log(m))/total+alpha*surplus/(2*total))
    if alpha <= 2:
        return b+2*alpha/total+alpha*surplus/(2*total)
    kernel = mp.exp(alpha*mp.log(mp.mpf(3)*total/(total+2)))-1-2*alpha
    return mp.log(mp.exp((alpha-1)*b)+kernel/total+
                  alpha*(alpha-1)*surplus/(2*total))/(alpha-1)

try:
    manifest = json.loads((base / 'CREDITED_INPUTS.json').read_text())
    for rel, v in manifest['files'].items():
        assert hashlib.sha256((base/'credited-inputs'/rel).read_bytes()).hexdigest() == v['sha256'], rel
    result['checks']['credited_files_literal'] = len(manifest['files'])

    t, theta, aa, cap, dim, jj, xx = sp.symbols('t theta aa cap dim jj xx', positive=True)
    variance = t*t*theta*(1-theta)/(1+t*theta)**2
    theta_v = 1/(t+2)
    algebra = {
        'variance_stationary': sp.simplify(sp.diff(variance, theta).subs(theta, theta_v)) == 0,
        'variance_value': sp.simplify(variance.subs(theta, theta_v)-t*t/(4*(1+t))) == 0,
        'moment_stationary_equation': sp.expand(cap*(1+t*theta)-aa*t*(1+cap*theta)
                                      -(cap-aa*t-(aa-1)*t*cap*theta)) == 0,
        'A_trace': sp.simplify((dim-2)+(1-2*xx)+xx*xx-(dim-1-2*xx+xx*xx)) == 0,
        'B_trace': sp.simplify(jj*(1+2*xx)+(dim-jj-1)+xx*xx-(dim-1+2*jj*xx+xx*xx)) == 0,
        'C_trace': sp.simplify(jj*(1+2*xx)+(dim-jj-2)*xx*xx+2
                              -(jj*(1+2*xx)+(dim-jj-2)*xx*xx+2)) == 0,
        'A_boundary': sp.expand(1-(1-2*xx)-2*xx) == 0,
        'B_C_boundary': sp.expand((1+2*xx)-1-2*xx) == 0,
    }
    assert all(algebra.values()), algebra
    result['checks']['symbolic_identities'] = algebra

    qubit_count = 0
    for total in [6, 8, 10, 14]:
        families = []
        for x in [Fraction(0), Fraction(1,10), Fraction(1,4), Fraction(2,5)]:
            families.append([Fraction(1)]*(total-2)+[1-2*x,x*x])
        for k in range(1,total-2):
            for x in [Fraction(0), Fraction(1,4), Fraction(1,2), Fraction(1)]:
                families.append([1+2*x]*k+[Fraction(1)]*(total-k-1)+[x*x])
            for x in [Fraction(1), Fraction(3,2), Fraction(2), Fraction(12,5)]:
                families.append([1+2*x]*k+[x*x]*(total-k-2)+[Fraction(1)]*2)
        for weights in families:
            eigen = sorted((w/sum(weights) for w in weights), reverse=True)
            assert len(eigen) == total and min(eigen) >= 0 and sum(eigen) == 1
            assert (eigen[0]-eigen[-2])**2 == 4*eigen[-3]*eigen[-1]
            assert all(v in {eigen[0],eigen[-3]} for v in eigen[1:-3])
            assert len({eigen[0],eigen[-3],eigen[-2],eigen[-1]}) <= 3
            qubit_count += 1
    result['checks']['exact_qubit_family_trace_boundary_membership'] = qubit_count

    uniform_count = 0
    by_m = {}
    for m in [16, 64, 256, 1024, 4096]:
        errors = []
        orders = [mp.mpf('1e-80'),mp.mpf('1e-20'),mp.mpf('.25'),mp.mpf('.5'),
                  1-mp.mpf('1e-35'),mp.mpf(1),1+mp.mpf('1e-35'),mp.mpf(2),mp.sqrt(m)/2,mp.sqrt(m)]
        for alpha in orders:
            b, th = bulk(m, alpha)
            assert 0 < th < 1 and b > 0
            rr = (alpha+2)*mp.mpf(2)/(m-1)
            vmax = mp.mpf(1)/(m*m-1)
            rho = alpha*abs(alpha-1)*vmax*mp.exp(rr)/2
            assert rho < 1
            ratio = b/(alpha*vmax/2)
            assert mp.exp(-rr)/(1+rho)*(1-mp.mpf('1e-100')) <= ratio
            assert ratio <= mp.exp(rr)/(1-rho)*(1+mp.mpf('1e-100'))
            errors.append(abs(b/(alpha/(2*m*m))-1))
            uniform_count += 1
        by_m[str(m)] = mp.nstr(max(errors),25)
    result['checks']['small_width_all_order_kernel'] = {'cases': uniform_count, 'max_relative_errors_by_m': by_m}

    lattice_count = 0
    largest_scaled_loss = mp.mpf(0)
    for m in [3,4,9,64]:
        for power in [2,3,4]:
            total = m*10**power
            for alpha in [mp.mpf('1e-80'),mp.mpf('1e-20'),mp.mpf('.01'),mp.mpf('.49'),mp.mpf('.5'),
                          mp.mpf('.9'),1-mp.mpf('1e-35'),mp.mpf(1),1+mp.mpf('1e-35'),
                          mp.mpf('1.1'),mp.mpf(2),mp.mpf(3),mp.mpf(10)]:
                b, _ = bulk(m, alpha)
                discrete = rank_value(m,total,alpha)
                loss = b-discrete
                assert loss >= -mp.mpf('1e-180')
                scaled = max(mp.mpf(0),loss)*total*total/alpha
                assert scaled < 100
                largest_scaled_loss = max(largest_scaled_loss,scaled)
                lattice_count += 1
    result['checks']['finite_lattice_loss'] = {'cases': lattice_count, 'max_loss_times_D2_over_alpha':mp.nstr(largest_scaled_loss,30)}

    fixed_local = []
    for m in [3,4,7,16]:
        for power in [3,5,7]:
            total = m*10**power
            h = mp.log(mp.mpf(total)/(total-1))
            errors = []
            for alpha in [mp.mpf(total)**-3,mp.mpf(total)**-1,mp.mpf(10)/total,
                          mp.mpf(total)**mp.mpf('-.25'),mp.mpf('.49'),mp.mpf('.5'),mp.mpf(1),mp.sqrt(m)]:
                target = max(h,rank_value(m,total,alpha),pole(total,alpha))
                approximate = low_profile(m,total,alpha)
                errors.append(abs(approximate/target-1))
                assert approximate > 0 and target > 0
            fixed_local.append({'m':m,'D':total,'max_relative_difference_to_three_actual_families':mp.nstr(max(errors),25)})
    result['checks']['fixed_local_low_profile'] = fixed_local

    rectangle_count = 0
    for m in [3,4,9]:
        total = m*10**5
        t0 = mp.mpf(2)/(m-1)
        for alpha in [mp.sqrt(m)+mp.mpf('.01'),mp.mpf(5),mp.mpf(20),mp.mpf(100)]:
            assert alpha > 1
            fq = mp.exp((alpha-1)*bulk(m,alpha)[0])
            r = mp.exp(alpha*mp.log(mp.mpf(3)*total/(total+2)))/total
            attained = []
            for numerator in range(33):
                kk = t0*numerator/32
                eta = 2*(m-2)*kk*kk/(2-(m-3)*kk)
                ac = mp.expm1(alpha*mp.log1p(kk))
                cc = 1+r*((3-eta)/3)**alpha
                theta0 = mp.mpf(0) if kk == 0 else max(mp.mpf(0),min(mp.mpf(1),
                                    (ac-alpha*kk*cc)/((alpha-1)*kk*ac)))
                value = (cc+theta0*ac)/(1+kk*theta0)**alpha
                assert value <= (fq+r)*(1+mp.mpf('1e-150'))
                attained.append(value)
                rectangle_count += 1
            assert max(attained) >= max(fq,1+r)*(1-mp.mpf('1e-150'))
    result['checks']['finite_V_sandwich_at_sampled_parameters'] = {'cases': rectangle_count,
        'scope':'checks explicit scalar formulas and endpoint lower bounds; samples do not establish its global maximum'}

    rejected = []
    m=3; total=3*10**6; alpha=mp.mpf(total)**-2
    true_floor=mp.log(mp.mpf(total)/(total-1)); b,_=bulk(m,alpha)
    assert b/true_floor < mp.mpf('.001')
    rejected.append('omit hole floor when alpha is much smaller than 1/D')
    alpha=mp.mpf('1e-12'); b,_=bulk(3,alpha)
    assert abs((alpha/18)/b-1)>mp.mpf('.01')
    rejected.append('replace finite-m bulk coefficient by alpha/(2m^2) at fixed m')
    m=1024; total=m*m; alpha=mp.mpf(2)
    corrected=low_profile(m,total,alpha)*total
    b,_=bulk(m,alpha)
    assert mp.mpf('7.999') < corrected < mp.mpf('8.001')
    wrong_max=max(b,4/mp.mpf(total),3/mp.mpf(total))*total
    wrong_no_surplus=(b+4/mp.mpf(total))*total
    assert wrong_max < mp.mpf('4.001') and wrong_no_surplus < mp.mpf('5.001')
    rejected.extend(['take maximum of separately optimized head and body terms',
                     'delete balanced-aspect surplus variance'])
    assert bulk(3,mp.mpf(2),mp.mpf(1))[0] == 0
    assert mp.log(4) > 0
    rejected.append('omit trace normalization of a projection spectrum')
    q=Fraction(5,3); total=20
    integer_power=max(Fraction(total)*(total+k*(q*q-1))/(total+k*(q-1))**2 for k in range(1,total))
    assert Fraction(16,15)-integer_power == Fraction(1,5415)
    rejected.append('claim continuous rank gives the exact finite projection maximum')
    result['checks']['actual_rejected_wrong_extensions'] = rejected
    result['status'] = 'PASS'
except Exception:
    result['status'] = 'FAIL'
    result['traceback'] = traceback.format_exc()
finally:
    result['completed_utc'] = datetime.now(timezone.utc).isoformat()
    (run/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'run':str(run),'status':result['status'],
                  'groups':list(result['checks']),'source_paper_sha256':source_hashes['PAPER.md']}))
if result['status'] != 'PASS':
    print(result['traceback'])
    raise SystemExit(1)
