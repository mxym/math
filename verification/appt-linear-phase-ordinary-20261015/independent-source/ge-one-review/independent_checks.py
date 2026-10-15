"""Independent reviewer diagnostics for D1; written without author-code imports.

The global proof is a mathematical read. These checks are finite algebraic and
numerical diagnostics and genuine expected-assertion countercontrols only.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, sys, traceback
import mpmath as mp
import sympy as sy

BASE = Path(__file__).resolve().parent
mp.mp.dps = 500
STAMP = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN = BASE / 'runs' / STAMP
RUN.mkdir(parents=True)
shutil.copyfile(__file__, RUN / 'executed_script.py')
RESULT = {'utc': STAMP, 'kind': 'independent internal AI reviewer diagnostics',
          'python': sys.version, 'mpmath': mp.__version__, 'sympy': sy.__version__,
          'decimal_precision': mp.mp.dps,
          'inputs': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in (BASE / 'PURE_ENVELOPE_GE_ONE.md', BASE / 'INPUT.json')},
          'author_code_imported_or_executed': False, 'groups': {},
          'finite_diagnostics_are_not_global_quantified_proof': True}

def q(x): return x / mp.expm1(x)
def s(x): return 1 + 1 / mp.expm1(x) - 1 / x
def g(x):
    if not x: return mp.mpf(0)
    return -mp.log(q(x)) - 1 + q(x)
def b(x): return mp.exp(g(x))
def aa(k, K): return 2 * k*k / (3*(K-k))
def profile(c, r, L, h):
    k = c*L
    B = mp.exp(-k*h)*(1+h*mp.expm1(k))
    P = mp.mpf(0) if L == 2 else mp.exp(-k*h - 2*c*L*L/(3*(2-L)))
    return B+r*P, B, P

def exact_algebra():
    t, K, u, k, r, a = sy.symbols('t K u k r a', positive=True)
    qq = t/(sy.exp(t)-1); ss = sy.exp(t)/(sy.exp(t)-1)-1/t
    gg = -sy.log(qq)-1+qq
    H = (t-2)*sy.exp(t)+t+2
    ac = 2*k*k/(3*(K-k))
    assertions = [
        sy.simplify(sy.diff(qq,t)+ss*qq),
        sy.simplify(sy.diff(gg,t)-ss*(1-qq)),
        sy.simplify(2*t*(sy.exp(t)-1)*(ss-sy.Rational(1,2))-H),
        sy.simplify(sy.diff(H,t,2)-t*sy.exp(t)),
        sy.simplify(sy.diff(ac,k)-2*k*(2*K-k)/(3*(K-k)**2)),
        sy.factor(2*K*K/(3*u)-u/6-K/2-(K-u)*(4*K+u)/(6*u)),
    ]
    E = sy.exp(k)-1
    hh = 1/k-(1+r*sy.exp(-a))/E
    assertions.append(sy.simplify(1+hh*E+r*sy.exp(-a)-E/k))
    assertions.append(sy.simplify(-k*hh-(-1+k/E+r*k*sy.exp(-a)/E)))
    for x in assertions: assert x == 0, x
    return {'symbolic_identities':len(assertions),
            'sign_proof_factors':'K-u, 4K+u, 6u are strictly positive for 0<u<K'}

def strict_and_convex():
    samples=[]; count=0
    for tx in ['1e-100','1e-25','.00001','.1','1','2','10','40']:
        t=mp.mpf(tx)
        assert s(t)>mp.mpf('.5')
        for factor in [mp.mpf('1.001'),mp.mpf('2'),mp.mpf('11')]:
            K=t*factor
            gap=g(K)-g(t)-(K-t)*s(t)*(1-q(t))
            assert gap>=0, (tx, factor, gap)
            count+=1
        samples.append({'t':tx,'s_minus_half':mp.nstr(s(t)-mp.mpf('.5'),18)})
    rational=0
    for KK in [sy.Rational(2),sy.Rational(2001,1000),sy.Rational(3),sy.Rational(20)]:
        for z in [sy.Rational(1,10**8),sy.Rational(1,100),sy.Rational(1,2),sy.Rational(99999999,10**8)]:
            uu=KK*z
            exact=2*KK*KK/(3*uu)-uu/6
            assert exact>KK/2>=1
            rational+=1
    return {'strict_s_samples':samples,'tangent_diagnostics':count,'exact_rational_strict_endpoint_cases':rational}

def envelope_checks():
    count=0; strict=0; endpoints=0
    for cx in ['1','1.00001','1.5','3','10']:
        c=mp.mpf(cx); bulk=b(2*c); r0=bulk-1
        hb=1/(2*c)-1/mp.expm1(2*c)
        for ratio in ['0','.5','1','1.001','3']:
            r=mp.mpf(ratio)*r0; envelope=max(bulk,1+r)
            for L in [mp.mpf(0),mp.mpf('1e-100'),mp.mpf('.2'),mp.mpf(1),2-mp.mpf('1e-100'),mp.mpf(2)]:
                for h in [mp.mpf(0),mp.mpf('1e-70'),mp.mpf('.3'),hb,mp.mpf('.9'),mp.mpf(1)]:
                    F,B,P=profile(c,r,L,h)
                    assert F<=envelope+mp.mpf('1e-350')*envelope,(cx,ratio,L,h)
                    count+=1
                    if 0<L<2 and h in [0,1] and ratio=='1':
                        assert F<bulk
                        strict+=1
            p=profile(c,r0,mp.mpf(0),mp.mpf('.3'))[0]
            z=profile(c,r0,mp.mpf(2),hb)[0]
            assert abs(p-bulk)<mp.mpf('1e-450')*bulk
            assert abs(z-bulk)<mp.mpf('1e-450')*bulk
            endpoints+=2
    return {'finite_profile_cases':count,'strict_positive_width_mixing_endpoint_cases':strict,
            'two_width_endpoint_attainment_diagnostics':endpoints,
            'full_scalar_argmax_proof':'written compactness/interior contradiction, not this grid'}

def false_variants():
    rejected=[]
    def reject(name, claim, witness):
        try:
            assert claim, name
        except AssertionError as ex:
            rejected.append({'name':name,'observed_exception':str(ex), 'witness':witness})
        else:
            raise AssertionError('countercontrol failed to reject: '+name)
    k=mp.mpf('.4');K=mp.mpf(2)
    reject('reverse the convex tangent inequality',
           g(K)-g(k)<=(K-k)*s(k)*(1-q(k)),{'k':'0.4','K':'2'})
    u=sy.Rational(1999,1000); KK=sy.Rational(2)
    value=2*KK*KK/(3*u)-u/6
    reject('replace the strict D6 bound at c=1 by equality', value==1,
           {'exact_value':str(value),'strictly_above':'1'})
    c=mp.mpf('.01');r=mp.mpf('.0003');L=mp.mpf('.85');h=mp.mpf('.365')
    FF=profile(c,r,L,h)[0]
    reject('extend the c>=1 theorem to every positive c', FF<=max(b(2*c),1+r),
           {'c':str(c),'r':str(r),'L':str(L),'h':str(h),
            'positive_excess':mp.nstr(FF-max(b(2*c),1+r),30)})
    K=mp.mpf(2); k=mp.mpf('.01');r=b(K)-1;ap=aa(k,K)
    hs=1/k-(1+r*mp.exp(-ap))/mp.expm1(k)
    formal=mp.exp(g(k)+r*q(k)*mp.exp(-ap))
    actual=(1+r*mp.exp(-ap))
    reject('use the interior eliminated value when its mixing parameter is negative',
           hs>=0 and abs(formal-actual)<mp.mpf('1e-100'),
           {'h_unconstrained':mp.nstr(hs,30),'formal_minus_constrained':mp.nstr(formal-actual,30)})
    c=mp.mpf(1);K=2*c;k=mp.mpf('.1');u=K-k
    reject('drop the protection derivative in the interior contradiction',
           u*s(k)>1, {'u_times_s_only':mp.nstr(u*s(k),30),
                       'u_times_s_plus_a_prime':mp.nstr(u*(s(k)+2*k*(2*K-k)/(3*u*u)),30)})
    # The maximally mixed density is APPT under every unitary, with zero body
    # spread. Its actual peak slack remains positive when r>0. No ansatz/grid
    # can justify deleting the physical loss from S.
    m=100;n=3**m//m;D=m*n;alpha=mp.mpf(m)
    actualmoment=mp.mpf(1);headslack=(mp.power(3,alpha)-1)/D
    reject('body law alone certifies positive-r near-optimality',
           headslack<mp.mpf('.01'),
           {'actual_state':'I/D, all-global-unitary APPT','body_spread':'0',
            'm':m,'n':str(n),'head_slack':mp.nstr(headslack,30),'actual_moment':str(actualmoment)})
    return {'expected_assertion_errors':rejected,'count':len(rejected)}

try:
    for name,fun in [('exact_algebra',exact_algebra),('strict_and_convex',strict_and_convex),
                     ('envelope_diagnostics',envelope_checks),('false_variants',false_variants)]:
        RESULT['groups'][name]=fun()
    RESULT['status']='PASS'
except BaseException:
    RESULT['status']='FAIL';RESULT['traceback']=traceback.format_exc()
finally:
    RESULT['executed_script_sha256']=hashlib.sha256((RUN/'executed_script.py').read_bytes()).hexdigest()
    (RUN/'RESULT.json').write_text(json.dumps(RESULT,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),'status':RESULT['status'],'groups':list(RESULT['groups'])}))
if RESULT['status']!='PASS':
    print(RESULT['traceback']);sys.exit(1)
