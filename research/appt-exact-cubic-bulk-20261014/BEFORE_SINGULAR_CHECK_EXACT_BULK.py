"""Finite controls for exact integer onset and relative entropy errors only."""
from pathlib import Path
from fractions import Fraction as Q
import importlib.util
import hashlib,json
import mpmath as mp
import sympy as sp

HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'appt-cubic-entropy-20261014/check_cubic.py'
spec=importlib.util.spec_from_file_location('credited_cubic_utilities',OLD)
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
mp.mp.dps=320

def mq(x):return mp.mpf(x.numerator)/x.denominator
def show(x):return mp.nstr(x,35)
def rank(a,D,kappa):
    ideal=D*old.theta(a,kappa)
    ks={max(0,min(D,int(mp.floor(ideal)))),max(0,min(D,int(mp.ceil(ideal))))}
    return max(ks,key=lambda k:old.entropy(a,D,kappa,k,[],[]))
def G(a,D,kappa):return old.entropy(a,D,kappa,rank(a,D,kappa),[],[])
def physical(m,p,b,c):
    kap=Q(2,m-1)-c/(m*m)
    assert kap>0
    pats=old.patterns(len(p),len(b))
    margins=[]
    for pat in pats:
        value=old.K(p,b,pat,2+kap)
        assert value is not None
        margins.append(c-kap*m*m*(2+kap)*value/(m-1))
    assert min(margins)>=0
    return kap,min(margins),len(pats)

def relative(a,D,kap,p,b,body):
    """Direct weighted raw powers, with optional interior clipped body."""
    # body entries are (multiplicity, raw value), summing to D.
    assert sum(n for n,y in body)==D
    Delta=sum(mq(v) for v in p)-sum(mq(v) for v in b)
    trace0=sum(n*y for n,y in body)
    trace=trace0+Delta
    if a==1:
        w0=sum(n*y*mp.log(y) for n,y in body)
        dw=sum((1+kap+mq(v))*mp.log(1+kap+mq(v))-(1+kap)*mp.log1p(kap) for v in p)
        dw+=sum((1-mq(v))*mp.log(1-mq(v)) if v!=1 else 0 for v in b)
        ey=w0/trace0-mp.log(trace0/D)
        ex=(w0+dw)/trace-mp.log(trace/D)
    else:
        w0=sum(n*y**a for n,y in body)
        dw=sum((1+kap+mq(v))**a-(1+kap)**a for v in p)
        dw+=sum((1-mq(v))**a-1 for v in b)
        ey=(mp.log(w0/D)-a*mp.log(trace0/D))/(a-1)
        ex=(mp.log((w0+dw)/D)-a*mp.log(trace/D))/(a-1)
    H=sum(old.psi(a,1+mq(v)) for v in p)+sum(old.psi(a,1-mq(v)) for v in b)
    T=sum(mq(v) for v in p+b)
    scale=kap*T+T*T/D
    return D*(ex-ey),H,abs(D*(ex-ey)-H)/scale if scale else mp.mpf(0)

def run():
    report={'scope':'finite ordinary supporting controls, no infinite/full-state or Lean certificate',
        'mpmath_digits':mp.mp.dps,'mpmath_version':mp.__version__,'sympy_version':sp.__version__,
        'retained_failed_controls':[]}
    D,k,u=sp.symbols('D k u')
    A=2*u+u*u
    diff=(D+k*A)*(D+(k+1)*u)**2-(D+(k+1)*A)*(D+k*u)**2
    expected=u*u*(-D*D+D*(2*k+1)+k*(k+1)*(u*u+2*u))
    assert sp.expand(diff-expected)==0
    report['exact_adjacent_rank_tie_identity']=str(sp.factor(diff))
    q,p,b=sp.symbols('q p b')
    positive=(2/(q-p)-2/q)/(2/(2-p)-1)
    negative=(1/(q-2*b)-1/q)/(1/(2-2*b)-sp.Rational(1,2))
    assert sp.factor(positive-2*(2-p)/(q*(q-p)))==0
    assert sp.factor(negative-4*(1-b)/(q*(q-2*b)))==0
    report['exact_disjoint_resolvent_ratios']=True
    ties=[]
    for kk in [2,5,50,500]:
        dd=2*kk+2;kap=mp.sqrt(1+mp.mpf(2)/kk)-1
        v0=old.entropy(mp.mpf(2),dd,kap,kk,[],[])
        v1=old.entropy(mp.mpf(2),dd,kap,kk+1,[],[])
        assert abs(v0-v1)<mp.mpf('1e-300')
        if dd<=102:
            assert all(old.entropy(mp.mpf(2),dd,kap,j,[],[])<=v0+mp.mpf('1e-300') for j in range(dd+1))
        ties.append({'D':dd,'ranks':[kk,kk+1],'kappa':show(kap),'moment_tie_error':show(v0-v1),
            'derivative_left_branch':show(mp.diff(lambda z:old.entropy(mp.mpf(2),dd,z,kk+1,[],[]),kap)),
            'derivative_right_branch':show(mp.diff(lambda z:old.entropy(mp.mpf(2),dd,z,kk,[],[]),kap))})
    report['integer_tie_controls']=ties
    interval_count=0
    for dd in [3,4,5,8,13]:
        for kap in [mp.mpf('0.03'),mp.mpf('0.2'),mp.mpf(1)]:
            for a in [mp.mpf('0.25'),mp.mpf('0.75'),mp.mpf(1),mp.mpf(2),mp.mpf(3)]:
                exact=G(a,dd,kap)
                direct=max(old.entropy(a,dd,kap,j,[],[]) for j in range(dd+1))
                assert abs(exact-direct)<mp.mpf('1e-300')
                for trial in range(3):
                    ys=[1+kap*((7*i+trial)%13)/12 for i in range(dd)]
                    mean=sum(ys)/dd
                    if a==1:value=sum(y*mp.log(y) for y in ys)/(dd*mean)-mp.log(mean)
                    else:value=(mp.log(sum(y**a for y in ys)/dd)-a*mp.log(mean))/(a-1)
                    assert value<exact
                    interval_count+=1
    kap=mp.mpf(1);dd=4
    cont=(mp.log(1+old.theta(mp.mpf(2),kap)*(mp.mpf(4)-1))-2*mp.log(1+kap*old.theta(mp.mpf(2),kap)))
    assert cont>G(mp.mpf(2),dd,kap)
    report['strict_integer_vs_continuous_control']={'D':4,'kappa':'1','continuous':show(cont),'exact_integer':show(G(mp.mpf(2),dd,kap)),'actual_APPT_claim':False}
    report['interval_only_convex_cone_and_integer_max_controls']=interval_count
    profiles=[([Q(1)],[]),([],[Q(1,2)]),([Q(1,3)],[Q(1,4)]),
        ([Q(1,4),Q(1,5)],[Q(1,6)]),([Q(1,10**30)],[]),([],[Q(1,10**80)])]
    records=[];slotchecks=0;relativechecks=0
    for pp,bb in profiles:
        C,_=old.cost(pp,bb,old.patterns(len(pp),len(bb)))
        assert C is not None
        c=C+max(C/Q(5),Q(1,10**90))
        for mm in [128,512]:
            kap,margin,npat=physical(mm,pp,bb,c);slotchecks+=npat
            for power in [0,20,80,120]:
                dd=mm**3*(10**power)
                for a in [mp.mpf('0.25'),mp.mpf('0.75'),mp.mpf(1),mp.mpf('1.00000001'),mp.mpf(2),mp.mpf(5)]:
                    rk=rank(a,dd,mq(kap))
                    assert rk>=mm*(mm-1)//2+len(pp) and dd-rk>=mm*(mm+1)//2+len(bb)
                    for tag in ['endpoint','interior_body']:
                        if tag=='endpoint':body=[(rk,1+mq(kap)),(dd-rk,mp.mpf(1))]
                        else:
                            top=mm*(mm-1)//2+len(pp)+2;bottom=mm*(mm+1)//2+len(bb)+2
                            body=[(top,1+mq(kap)),(bottom,mp.mpf(1)),(dd-top-bottom,1+mq(kap)/3)]
                        value,H,ratio=relative(a,dd,mq(kap),pp,bb,body)
                        assert ratio<100
                        records.append({'m':mm,'D_power':power,'alpha':str(a),'p':list(map(str,pp)),
                            'beta':list(map(str,bb)),'body':tag,'relative_error_over_kappaT_plus_T2_overD':show(ratio),
                            'all_pattern_exact_margin':str(margin)})
                        relativechecks+=1
    report['exact_finite_pattern_checks']=slotchecks
    report['tiny_head_unbounded_D_relative_checks']=relativechecks
    report['relative_controls']=records
    lower=[];upper=[]
    for mm in [256,512,1024,2048]:
        pp=[Q(1)];bb=[];cc=Q(4)+Q(32,mm)
        kap,margin,npat=physical(mm,pp,bb,cc)
        for side,aa in [('below',-8),('above',8)]:
            nn=mm*mm//4+aa*mm;dd=mm*nn;assert nn>=mm
            rk=rank(mp.mpf(2),dd,mq(kap))
            profit=dd*(old.entropy(mp.mpf(2),dd,mq(kap),rk,pp,bb)-G(mp.mpf(2),dd,mq(Q(2,mm-1))))
            record={'m':mm,'n':nn,'n_minus_m2_over4_in_units_m':aa,'actual_profit':show(profit),
                'm_times_profit':show(mm*profit),'cost_budget':str(cc),'exact_APPT_margin':str(margin)}
            if side=='below':assert profit>0;lower.append(record)
            else:assert profit<0;upper.append(record)
    report['alpha2_actual_Om_lower_controls']=lower
    report['alpha2_same_head_above_band_controls']=upper
    # Unsafe linearization of the extensive moment creates a false winner.
    mm=128;dd=mm**3*10**80;pp=[Q(1,10**30)];bb=[]
    C,_=old.cost(pp,bb,old.patterns(1,0));cc=C*Q(6,5)
    kap,margin,_=physical(mm,pp,bb,cc);a=mp.mpf(2);rk=rank(a,dd,mq(kap))
    actual=old.entropy(a,dd,mq(kap),rk,pp,bb);benchmark=G(a,dd,mq(Q(2,mm-1)))
    mean=1+(rk*mq(kap)+mq(pp[0]))/dd
    rawpowers=(rk-1)*(1+mq(kap))**2+(1+mq(kap)+mq(pp[0]))**2+dd-rk
    extensive=(rawpowers/mean**2)-dd
    trueprofit=dd*(actual-benchmark);unsafeprofit=extensive-dd*benchmark
    assert trueprofit<0<unsafeprofit
    report['rejected_extensive_linearization_false_winner']={'m':mm,'D':str(dd),'tiny_head':str(pp[0]),
        'true_exact_entropy_profit':show(trueprofit),'unsafe_linearized_profit':show(unsafeprofit),
        'scope':'actual APPT finite state; rejects an uncanceled extensive baseline approximation'}
    report['implementation_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['credited_utility_sha256']=hashlib.sha256(OLD.read_bytes()).hexdigest()
    (HERE/'FINITE_CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['relative_controls']},indent=2))

if __name__=='__main__':run()
