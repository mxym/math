#!/usr/bin/env python3
"""New J review controls, distinct from the author's checks.py.

Global uniqueness and all physical quantifiers are audited in J_REVIEW.md;
finite calculus tests and a non-rigorous numerical crossing support that read.
"""
from pathlib import Path
from datetime import datetime, timezone
import json,hashlib,traceback
import sympy as s
from mpmath import mp

ROOT=Path(__file__).resolve().parent
RUN=ROOT/'j-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
out={'status':'RUNNING','independent_of_author':True,'Lean':False,
     'written_by':'resumed independent review agent','source':{},'groups':{}}
for folder in ('H','I','J'):
    for p in (ROOT/'snapshot'/folder).glob('*'):
        if p.is_file():
            out['source'][str(p.relative_to(ROOT/'snapshot'))]=hashlib.sha256(p.read_bytes()).hexdigest()
(RUN/'j_independent_checks.py').write_bytes(Path(__file__).read_bytes())
def save(): (RUN/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(test,msg):
    if not test:raise AssertionError(msg)
def eq(a,b,msg):need(s.simplify(a-b)==0,msg)
def group(n,f):
    print('START '+n,flush=True); out['groups'][n]=f(); save(); print('PASS '+n,flush=True)

def symbolic():
    a,x=s.symbols('alpha x',positive=True)
    identities=0
    for sign,width,den in ((1,2,2),(-1,1,1)):
        y=1+sign*x; ff=(y**a-1-a*(y-1))/(a-1)
        rr=(width-x)*ff/(den*a*x)
        F=x*(width-x)*s.diff(ff,x)-width*ff
        G=(width-x)*s.diff(ff,x,2)-2*s.diff(ff,x)
        eq(s.diff(rr,x),F/(den*a*x*x),'ratio derivative');identities+=1
        eq(s.diff(F,x),x*G,'F derivative');identities+=1
        gp=a*(1+x)**(a-3)*(2*a-7-(a+1)*x) if sign==1 else -a*(a+1)*(1-x)**(a-2)
        eq(s.diff(G,x),gp,'G derivative');identities+=1
        f1=y*s.log(y)-y+1
        r1=(width-x)*f1/(den*x)
        F1=x*(width-x)*s.diff(f1,x)-width*f1
        G1=(width-x)*s.diff(f1,x,2)-2*s.diff(f1,x)
        eq(s.diff(r1,x),F1/(den*x*x),'vN ratio derivative');identities+=1
        eq(s.diff(F1,x),x*G1,'vN F derivative');identities+=1
        eq(s.diff(G1,x),gp.subs(a,1),'vN G derivative');identities+=1
        # At any stationary point R''=G/(den*alpha*x).
        eq(s.diff(F/(den*a*x*x),x)-G/(den*a*x),-2*F/(den*a*x**3),'stationary curvature');identities+=1
    eq(s.Rational(56,81)-s.Rational(1,2),s.Rational(31,162),'log lower difference');identities+=1
    need(s.Rational(31,162)>s.Rational(3,16),'positive rational gap')
    need(s.Rational(179,80)**2>5,'negative square-root gap')
    return {'exact_derivative_identities':identities,'exact_inequality_controls':2}

mp.dps=160
def fmt(x):return mp.nstr(x,40)
def psi(a,y):
    if a==1:return y*mp.log(y)-y+1
    return (mp.expm1(a*mp.log(y))-a*(y-1))/(a-1)
def ratio(a,x,sign):
    return (2-x)*psi(a,1+x)/(2*a*x) if sign==1 else (1-x)*psi(a,1-x)/(a*x)
def crit(a,sign):
    lo=mp.mpf('1e-12'); hi=(2 if sign==1 else 1)-mp.mpf('1e-40')
    derivative=lambda x:mp.diff(lambda u:ratio(a,u,sign),x)
    need(derivative(lo)>0 and derivative(hi)<0,'direct derivative endpoint signs')
    for _ in range(360):
        x=(lo+hi)/2
        if derivative(x)>0:lo=x
        else:hi=x
    return (lo+hi)/2
def monotonic_controls():
    orders=list(map(mp.mpf,('.00000001','.001','.05','.5','.8','1','2','3.499999','3.5','3.500001','4','20','500')))
    orders+= [1-mp.mpf('1e-25'),1+mp.mpf('1e-25')]
    orders=sorted(orders)
    previous=None;rows=[]
    for a in orders:
        values=[]
        for sign in (1,-1):
            x=crit(a,sign); val=ratio(a,x,sign)
            curvature=mp.diff(lambda xx:ratio(a,xx,sign),x,2)
            need(curvature<0,'direct negative curvature')
            if sign==1:
                integral=x*(2-x)/2*mp.quad(lambda t:(1-t)*(1+t*x)**(a-2)*mp.log(1+t*x),[0,1])
            else:
                integral=x*(1-x)*mp.quad(lambda t:(1-t)*(1-t*x)**(a-2)*mp.log(1-t*x),[0,1])
            # mp.diff through the raw quotient at its removable alpha=1
            # singularity loses accuracy. Its exact alpha derivative there
            # follows from y**alpha to second order; compare it independently
            # with the integral. Both actual failed runs remain preserved.
            if a==1:
                y=1+sign*x
                pref=(2-x)/(2*x) if sign==1 else (1-x)/x
                partial=pref*(y*mp.log(y)**2/2-psi(a,y))
            else:
                partial=mp.diff(lambda aa:ratio(aa,x,sign),a)
            need(abs(partial-integral)<mp.mpf('1e-90')*max(1,abs(partial)),
                 'integral strict envelope derivative: alpha='+fmt(a)+' sign='+str(sign)+
                 ' direct='+fmt(partial)+' integral='+fmt(integral))
            need(integral>0 if sign==1 else integral<0,'strict integral sign')
            values.append(val)
            rows.append({'alpha':fmt(a),'sign':sign,'critical_mass':fmt(x),'critical_value':fmt(val),
                         'curvature':fmt(curvature),'envelope_slope':fmt(integral)})
        if previous:need(values[0]>previous[0] and values[1]<previous[1],'branch value monotonicity')
        previous=values
    need(abs(crit(mp.mpf(2),1)-1)<mp.mpf('1e-95'),'purity positive critical anomaly')
    need(abs(crit(mp.mpf('.5'),-1)-(mp.sqrt(5)-1)/2)<mp.mpf('1e-95'),'half negative critical anomaly')
    return {'precision_digits':mp.dps,'fixed_order_two_sign_cases':len(rows),'rows':rows,
            'scope':'finite derivative/integral controls, not an all-order root-count proof'}

def transition():
    # Solve the three independent stationary/equal-value equations together,
    # rather than recycle the author's nested bisection calculation.
    aa=mp.mpf('.55');p0=crit(aa,1);b0=crit(aa,-1)
    p,b,a=mp.findroot((lambda p,b,a:mp.diff(lambda x:ratio(a,x,1),p),
                     lambda p,b,a:mp.diff(lambda x:ratio(a,x,-1),b),
                     lambda p,b,a:ratio(a,p,1)-ratio(a,b,-1)),(p0,b0,aa),tol=mp.mpf('1e-125'))
    need(mp.mpf('.5')<a<1 and 0<p<2 and 0<b<1,'transition not interior')
    cp=mp.diff(lambda x:ratio(a,x,1),p,2);cm=mp.diff(lambda x:ratio(a,x,-1),b,2)
    slope=mp.diff(lambda al:ratio(al,p,1)-ratio(al,b,-1),a)
    need(cp<0 and cm<0 and slope>0,'transition degeneracy control')
    need(abs(ratio(a,p,1)-ratio(a,b,-1))<mp.mpf('1e-120'),'numeric equal value')
    # These are illustrative diagnostics only. No rational enclosure or exact
    # value of alpha_x is inferred from the floating-point system solve.
    return {'alpha_crossing_illustration':fmt(a),'critical_positive_mass':fmt(p),
            'critical_negative_mass':fmt(b),'leading_value':fmt(ratio(a,p,1)),
            'transverse_difference_slope':fmt(slope),'rigorous_interval_certificate':False}

def wrong_variants():
    # G_+ is not decreasing for every order. For alpha=10 its derivative at
    # p=0 is positive; the actual proof must retain its turning point.
    need(10*(2*10-7)>0,'all-order G monotonicity mutation not rejected')
    # For alpha=1 and alpha<1 the negative endpoint G is unbounded below,
    # rather than having the finite alpha>1 endpoint value.
    def G(a,y):
        if a==1:return 1+2*mp.log(y)
        return -a*(a+1)*y**(a-1)/(1-a)+2*a/(1-a)
    need(G(mp.mpf('.5'),mp.mpf('1e-80'))<-mp.mpf('1e30'),'singular negative endpoint mutation')
    need(G(mp.mpf(1),mp.mpf('1e-80'))<-100,'vN endpoint mutation')
    raw_division_failed=False
    try:
        alpha=mp.mpf(1); y=mp.mpf('.7')
        _=(y**alpha-1-alpha*(y-1))/(alpha-1)
    except ZeroDivisionError:
        raw_division_failed=True
    need(raw_division_failed,'raw alpha=1 quotient shortcut did not fail')
    return {'rejected':['G_positive strictly decreasing at every positive order',
                        'finite negative endpoint G for alpha<=1',
                        'alpha=1 covered by raw division by alpha-1'],
            'scope':'explicit counterexamples to proof shortcuts; analytic endpoint analysis is still required'}

save()
try:
    group('exact_calculus',symbolic)
    group('independent_critical_derivatives',monotonic_controls)
    group('simultaneous_transition_control',transition)
    group('adversarial_shortcuts',wrong_variants)
    out['status']='PASS'
except BaseException as e:
    out['status']='FAIL';out['error']=str(e);out['traceback']=traceback.format_exc();print(out['traceback'],flush=True)
finally:
    out['ended_utc']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps({'status':out['status'],'run':str(RUN)}),flush=True)
if out['status']!='PASS':raise SystemExit(1)
