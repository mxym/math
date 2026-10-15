"""New independent diagnostics for B1--B19; no author code is imported.

Exact identities support a separate full mathematical read. Finite stationary
points and integer-state samples do not certify the quantified APPT optimum.
All executions, including any unexpected failure, retain their exact script.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, sys, traceback
import mpmath as mp
import sympy as sy

BASE=Path(__file__).resolve().parent
mp.mp.dps=400
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_script.py')
RESULT={'utc':STAMP,'kind':'independent internal AI reviewer diagnostics',
        'python':sys.version,'mpmath':mp.__version__,'sympy':sy.__version__,
        'decimal_precision':mp.mp.dps,'inputs':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [BASE/'PAPER_V1.md',BASE/'INPUT.json']},
        'author_code_imported_or_executed':False,'groups':{},
        'finite_stationary_or_ansatz_samples_do_not_prove_global_quantifiers':True}

def q(k):return k/mp.expm1(k) if k else mp.mpf(1)
def g(k):return -mp.log(q(k))-1+q(k)
def b(k):return mp.exp(g(k))
def ab(c,L):return 2*c*L*L/(3*(2-L))
def mix(c,L):
    k=c*L
    return (mp.log(mp.expm1(k)/k)-g(2*c))/k
def raw(c,L,h):
    if L==0:return b(2*c)-1
    k=c*L
    return mp.exp(ab(c,L))*(b(2*c)*mp.exp(k*h)-1-h*mp.expm1(k))
def reduced(c,L):
    if not L:return b(2*c)-1,mp.mpf(0)
    hh=max(mp.mpf(0),mix(c,L));k=c*L
    if hh==0:return mp.exp(ab(c,L))*(b(2*c)-1),hh
    return mp.exp(ab(c,L))*(g(2*c)-g(k))/q(k),hh
def phi(c,t):
    k=2*c-c*c*t
    return (g(2*c)-g(k))*mp.exp(2*(2-c*t)**2/(3*t))/(c**3*q(k))
def branch(c):
    tt=mp.findroot(lambda t:mp.diff(lambda x:phi(c,x),t),
                   (mp.mpf('2.5'),mp.mpf('2.9')),tol=mp.mpf('1e-320'))
    L=2-c*tt;hh=mix(c,L);rr=c**3*phi(c,tt)
    return tt,L,hh,rr
def scalar(c,r,L,h):
    k=c*L
    B=mp.exp(-k*h)*(1+h*mp.expm1(k))
    P=mp.mpf(0) if L==2 else mp.exp(-k*h-ab(c,L))
    return B+r*P,B,P

def symbolic():
    k,K,h,a=sy.symbols('k K h a',positive=True)
    c,t=sy.symbols('c t',positive=True)
    A=(sy.exp(k)-1)/k;qq=1/A;gb=sy.symbols('gb',real=True)
    U=sy.exp(a)*(sy.exp(gb+k*h)-1-h*(sy.exp(k)-1))
    hstar=(sy.log(A)-gb)/k
    checks=[sy.simplify(sy.diff(U,h,2)-sy.exp(a+gb+k*h)*k*k),
            sy.simplify(sy.diff(U,h).subs(h,hstar)),
            sy.simplify(U.subs(h,hstar)-sy.exp(a)*(gb-(sy.log(A)-1+qq))/qq)]
    x=sy.symbols('x')
    gseries=sy.series(sy.log((sy.exp(x)-1)/x)-1+x/(sy.exp(x)-1),x,0,7).removeO()
    checks.append(sy.expand(gseries-(x*x/8-x**4/576+x**6/25920)))
    kk=2*c-c*c*t
    gdifference=sy.series((gseries.subs(x,2*c)-gseries.subs(x,kk))/c**3,c,0,2).removeO()
    checks.append(sy.expand(gdifference-(t/2-c*t*t/8)))
    expfactor=1-sy.Rational(8,3)*c
    invqfactor=1+c
    phifirst=sy.series(gdifference*expfactor*invqfactor,c,0,2).removeO()
    checks.append(sy.expand(phifirst-(t/2+c*(-t*t/8-5*t/6))))
    psi=t*sy.exp(8/(3*t))/2;first=sy.exp(8/(3*t))*(-t*t/8-5*t/6);t0=sy.Rational(8,3)
    checks += [sy.simplify(sy.diff(psi,t).subs(t,t0)),
               sy.simplify(sy.diff(psi,t,2).subs(t,t0)-3*sy.E/16),
               sy.simplify(first.subs(t,t0)+28*sy.E/9),
               sy.simplify(sy.diff(first,t).subs(t,t0)+sy.E/3),
               sy.simplify(-sy.diff(first,t).subs(t,t0)/sy.diff(psi,t,2).subs(t,t0)-sy.Rational(16,9))]
    logA=kk/2+kk**2/24-kk**4/2880
    hser=sy.series((logA-gseries.subs(x,2*c))/kk,c,0,3).removeO()
    checks.append(sy.expand(hser-(sy.Rational(1,2)-c/6-t*c*c/6)))
    B,P,bb=sy.symbols('B P bb')
    checks.append(sy.factor(P*((bb-B)/P)+(1-P)*((B-1)/(1-P))-(bb-1)))
    for z in checks:assert z==0,z
    return {'exact_symbolic_identities':len(checks),'independently_derived_B7':{
          't_prime':'16/9','L_c2':'-16/9','h_c2':'-4/9',
          'r_c3':'4e/3','r_c4':'-28e/9','psi_curvature':'3e/16'}}

def mixing_and_bounds():
    clamped=0;interior=0;compares=0;gaps=0;identities=0
    for cx in ['.000001','.001','.01','.1','1','3','10']:
        c=mp.mpf(cx)
        for Lx in ['.000001','.01','.4','1','1.9','1.999999']:
            L=mp.mpf(Lx);v,hh=reduced(c,L)
            assert 0<=hh<1
            assert abs(v-raw(c,L,hh))<mp.mpf('1e-320')*max(1,abs(v))
            clamped+=hh==0;interior+=hh>0
            for h in [mp.mpf(0),mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.9'),mp.mpf(1)]:
                assert raw(c,L,h)>=v-mp.mpf('1e-320')*max(1,abs(v))
                compares+=1
            F,B,P=scalar(c,mp.mpf('.003'),L,mp.mpf('.37'))
            uu=raw(c,L,mp.mpf('.37'));Q=(B-1)/(1-P)
            assert abs(P*uu+(1-P)*Q-(b(2*c)-1))<mp.mpf('1e-320')*max(1,abs(uu))
            identities+=1
    for cx in ['.00000001','.00001','.001','.01']:
        c=mp.mpf(cx)
        for Lx in ['0','.01','.5','1','1.8','1.99999']:
            L=mp.mpf(Lx)
            for hx in ['0','.27','.5','1']:
                F,B,P=scalar(c,0,L,mp.mpf(hx))
                assert b(2*c)-B>=c*c*(2-L)/8
                gaps+=1
    boundary=[]
    for tx in ['.3','.1','.03','.01']:
        t=mp.mpf(tx);bound=t/8*mp.exp(2/(3*t))
        boundary.append({'t':tx,'rescaled_lower_bound':mp.nstr(bound,25)})
    return {'clamped_widths':clamped,'interior_widths':interior,'mixing_comparisons':compares,
            'exact_weighted_threshold_identity_diagnostics':identities,
            'global_gap_diagnostics':gaps,'thin_layer_lower_bound_diagnostics':boundary,
            'global_tightness_is_analytic_not_certified_by_samples':True}

def branch_and_hessian():
    rows=[]
    for cx in ['.01','.003','.001','.0001','.000001','1e-20']:
        c=mp.mpf(cx);t,L,h,r=branch(c)
        assert 0<L<2 and 0<h<1 and 0<r<b(2*c)-1
        assert abs(t-(mp.mpf(8)/3+mp.mpf(16)/9*c))<4*c*c
        assert abs(h-(mp.mpf('.5')-c/6-mp.mpf(4)/9*c*c))<2*c**3
        assert abs(r-(mp.mpf(4)*mp.e/3*c**3-mp.mpf(28)*mp.e/9*c**4))<20*c**5
        F,B,P=scalar(c,r,L,h)
        assert abs(F-b(2*c))<mp.mpf('1e-310')
        rr=mp.diff(lambda x:phi(c,x),t,2)
        assert rr>0
        uhh=mp.exp(ab(c,L)+g(2*c)+c*L*h)*(c*L)**2
        widthschur=c*rr
        assert uhh>0 and widthschur>0
        assert abs(P/mp.e**(-1)-1)<3*c
        right=P/b(2*c)
        assert abs(right-mp.e**(-1))<c
        rows.append({'c':cx,'t':mp.nstr(t,35),'L':mp.nstr(L,35),'h':mp.nstr(h,35),
                     'r_over_c3':mp.nstr(r/c**3,35),'log_right_slope':mp.nstr(right,35),
                     'positive_hessian_schur':mp.nstr(widthschur,25)})
    return {'stationary_branch_diagnostics':rows,
            'global_uniqueness_basis':'written global compactness plus analytic IFT, not findroot'}

def integer_states():
    rows=[]
    c=mp.mpf('.01');t,L,h,r=branch(c)
    target=b(2*c);peak_target=r*mp.exp(-c*(L*h+2*L*L/(3*(2-L))))
    height_target=3*(L*h+2*L*L/(3*(2-L)))
    previous_moment_error=None;previous_height_error=None
    for m in [3000,9000,18000]:
        alpha=c*m
        n=int(mp.nint(mp.power(3,alpha)/(m*r)));D=m*n
        rank=max(m**3,min(D-m**3,int(mp.floor(h*D))))
        assert m<=n and m**3<=rank<=D-m**3
        kap=L/(m-1)
        eta=2*(m-2)*kap**2/(2-(m-3)*kap)
        d=2-kap-eta
        assert d>=0
        Z=D+kap*rank+d;z=Z/D
        head=(3-eta)/z;up=(1+kap)/z;lo=1/z
        trace=(head+(rank-1)*up+(D-rank)*lo)/D
        assert abs(trace-1)<mp.mpf('1e-350')
        moment=(head**alpha+(rank-1)*up**alpha+(D-rank)*lo**alpha)/D
        pe=head**alpha/D;he=m*(3-head)
        err=abs(moment-target);herr=abs(he-height_target)
        if previous_moment_error is not None:
            assert err<previous_moment_error and herr<previous_height_error
        previous_moment_error=err;previous_height_error=herr
        rows.append({'m':m,'n_digits':len(str(n)),'D_digits':len(str(D)),
              'projection_rank_digits':len(str(rank)),'alpha':str(alpha),
              'trace_error':mp.nstr(abs(trace-1),12),'moment_error':mp.nstr(err,30),
              'head_height_error':mp.nstr(herr,30),'actual_peak_moment':mp.nstr(pe,30),
              'fixed_c_peak_limit':mp.nstr(peak_target,30)})
    return {'exact_integer_rank_normalized_family_diagnostics':rows,
            'all_global_unitary_APPT_justification':'credited analytic Schmidt SOS for actual I+kappa P+d vv*, not sampled unitaries',
            'full_nearoptimizer_iff':'retains all S argmax/spread/peak hypotheses; not proved by finite family'}

def false_variants():
    rejected=[]
    def reject(name,claim,witness):
        try:assert claim,name
        except AssertionError as ex:rejected.append({'name':name,'observed_exception':str(ex),'witness':witness})
        else:raise AssertionError('countercontrol failed to reject '+name)
    c=mp.mpf('.0001');t,L,h,r=branch(c)
    reject('replace first coexistence by the bare quadratic crossing',
        abs(r-(b(2*c)-1))<r/10,{'r_over_bare_crossing':mp.nstr(r/(b(2*c)-1),30)})
    wrong=mp.mpf(4)*mp.e/3*c**3+mp.mpf(28)*mp.e/9*c**4
    reject('reverse the quartic threshold correction',abs(r-wrong)<20*c**5,
           {'wrong_minus_actual_over_c4':mp.nstr((wrong-r)/c**4,30)})
    reject('force mixing equal to one half before expanding the threshold',
           raw(c,L,mp.mpf('.5'))<=r,
           {'strict_positive_threshold_error':mp.nstr(raw(c,L,mp.mpf('.5'))-r,30)})
    k=mp.mpf('.001');K=mp.mpf(2);c1=K/2;LL=k/c1
    hs=mix(c1,LL);formal=mp.exp(ab(c1,LL))*(g(K)-g(k))/q(k)
    actual=raw(c1,LL,mp.mpf(0))
    reject('apply the interior logarithmic elimination to a clamped mixing minimum',
           abs(formal-actual)<mp.mpf('1e-100'),
           {'negative_unconstrained_h':mp.nstr(hs,30),'formal_minus_actual':mp.nstr(formal-actual,30)})
    missing_q=r*q(c*L)
    reject('omit the reciprocal-q factor in B6 and retain the quartic coefficient',
           abs(missing_q-r)<c**5,
           {'difference_over_c4':mp.nstr((missing_q-r)/c**4,30)})
    no_protection=r*mp.exp(-ab(c,L))
    reject('delete the protection exponential from the lower threshold',
           abs(no_protection-r)<c**4,
           {'ratio':mp.nstr(no_protection/r,30)})
    reject('merge the two coexistence thresholds when c is small',r>=b(2*c)-1,
           {'r_bulk':mp.nstr(r,30),'bare':mp.nstr(b(2*c)-1,30)})
    reject('set the pure-bulk surviving peak moment equal to its positive-r interior value',
           scalar(c,r,mp.mpf(2),mp.mpf('.5'))[2]>0,
           {'exact_P_at_width_2':'0','interior_peak_limit':mp.nstr(r*mp.exp(-c*(L*h+2*L*L/(3*(2-L)))),30)})
    return {'expected_assertion_errors':rejected,'count':len(rejected)}

try:
    for name,fun in [('symbolic',symbolic),('convex_elimination_and_global_bounds',mixing_and_bounds),
                     ('analytic_branch_diagnostics',branch_and_hessian),('integer_state_diagnostics',integer_states),
                     ('false_variants',false_variants)]:
        RESULT['groups'][name]=fun()
    RESULT['status']='PASS'
except BaseException:
    RESULT['status']='FAIL';RESULT['traceback']=traceback.format_exc()
finally:
    RESULT['executed_script_sha256']=hashlib.sha256((RUN/'executed_script.py').read_bytes()).hexdigest()
    (RUN/'RESULT.json').write_text(json.dumps(RESULT,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),'status':RESULT['status'],'groups':list(RESULT['groups'])}))
if RESULT['status']!='PASS':print(RESULT['traceback']);sys.exit(1)
