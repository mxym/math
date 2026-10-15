#!/usr/bin/env python3
"""Independent finite diagnostics for the NEW moving-order K proof.

Controls support, and do not replace, the full feasible-set/uniform proof.
No original author control script is executed by this file.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,traceback
import sympy as sy
from mpmath import mp

ROOT=Path(__file__).resolve().parent
RUN=ROOT/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
out={'status':'RUNNING','independent_of_author':True,'Lean':False,
     'full_feasible_set_enumeration':False,'source':{},'groups':{}}
for p in sorted((ROOT/'snapshot').rglob('*')):
    if p.is_file():out['source'][str(p.relative_to(ROOT/'snapshot'))]={
        'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines())}
(RUN/'independent_checks.py').write_bytes(Path(__file__).read_bytes())
def save():(RUN/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(test,msg):
    if not test:raise AssertionError(msg)
def eq(a,b,msg):need(sy.simplify(a-b)==0,msg)
def group(name,fn):
    print('START '+name,flush=True);out['groups'][name]=fn();save();print('PASS '+name,flush=True)

def formal_expansion():
    ep,z,al,u,d,a,P,Pa,J,b4=sy.symbols('epsilon z alpha0 u d0 a P P_alpha J b4')
    t=2*ep/(1-ep);r=2*ep/(1+(z-1)*ep);moving=al+u*ep
    B=lambda x:moving*x*x/8-moving*x**3/8+b4*x**4
    delta=sy.series(B(r)-B(t),ep,0,5).removeO()
    eq(delta,-al*z*ep**3+(sy.Rational(3,2)*al*z*z-u*z)*ep**4,'moving contrast difference')
    base=sy.series((d+a*ep)*delta/ep**3+P+ep*(u*Pa+2*J),ep,0,2).removeO()
    Q=P-al*d*z
    R=2*J+sy.Rational(3,2)*al*d*z*z-al*a*z+u*(Pa-d*z)
    eq(base,Q+ep*R,'full moving Q and R')
    A,sigma=sy.symbols('A sigma')
    subst={Pa:z*d+al*z*sigma,J:(al*z*A-sy.Rational(3,2)*al*d*z*z)/2}
    eq(R.subs(subst),al*z*(A+sigma*u-a),'critical affine value')
    # Size of integer score loss and displacement from m-curvature.
    m=sy.symbols('m',positive=True)
    eq(m*(d*m**3)*(m**-2/(d*m**3)**2),m**-4/d,'rank error scaling')
    eq(sy.sqrt(m**-4/m),m**-sy.Rational(5,2),'discrete scalar displacement scaling')
    return {'exact_symbolic_checks':5,'derived_full_R':str(R),
            'scope':'formal expansion coefficients and scaling; analytic remainder audited separately'}

mp.dps=330
def fmt(x):return mp.nstr(x,38)
def psi(al,y):
    if not y:return mp.mpf(1)
    return (mp.expm1(al*mp.log(y))-al*(y-1))/(al-1)
def dp(al,y):return al*mp.expm1((al-1)*mp.log(y))/(al-1)
def da_psi(al,y):
    num=mp.expm1(al*mp.log(y))-al*(y-1)
    return ((al-1)*(y**al*mp.log(y)-(y-1))-num)/(al-1)**2
def limiting(al,z,sign):
    h=2*z/(z+2) if sign==1 else -z/(1+z)
    P=psi(al,1+h)
    J=((1 if sign==1 else 0)+h/2)*dp(al,1+h)-al*(h+P)/2
    return h,P,J
def ratio(al,x,sign):
    return (2-x)*psi(al,1+x)/(2*al*x) if sign==1 else (1-x)*psi(al,1-x)/(al*x)
pstar,bstar,alpha0=mp.findroot((lambda p,b,al:mp.diff(lambda x:ratio(al,x,1),p),
                               lambda p,b,al:mp.diff(lambda x:ratio(al,x,-1),b),
                               lambda p,b,al:ratio(al,p,1)-ratio(al,b,-1)),
                              (mp.mpf('.85'),mp.mpf('.61'),mp.mpf('.55')),tol=mp.mpf('1e-260'))
zs={1:2*pstar/(2-pstar),-1:bstar/(1-bstar)}
d0=ratio(alpha0,pstar,1)
As={};sigmas={}
for sign,z in zs.items():
    h,P,J=limiting(alpha0,z,sign)
    As[sign]=2*J/(alpha0*z)+3*P/(2*alpha0)
    sigmas[sign]=(alpha0*da_psi(alpha0,1+h)-P)/(alpha0**2*z)

def body(al,r):
    Q=mp.expm1(al*mp.log1p(r));ss=al*(Q-r)/((al-1)*Q)
    return mp.log(Q/(al*r))/(al-1)-mp.log(ss)
def data(al,m,z,sign):
    r=mp.mpf(2)/(m-1+z);q=1+r
    h=(2+r)*z/(z+2) if sign==1 else -(2+r)*z/(2*(1+z))
    Q=mp.expm1(al*mp.log(q));H=(q+h)**al-q**al if sign==1 else (1+h)**al-1
    g=(r*H-Q*h)/(Q-r)
    return r,Q,h,H,g
def score(al,hist,D):
    S=mp.fsum(x*c for x,c in hist);W=mp.fsum(x**al*c for x,c in hist)
    return (mp.log(W/D)-al*mp.log(S/D))/(al-1)
def family(al,m,D,z,sign,k=None):
    r,Q,h,H,g=data(al,m,z,sign)
    if k is None:return body(al,r)-mp.log1p(-g/D)
    hist=[(1+r,k),(mp.mpf(1),D-k)]+([(1+r,-1),(1+r+h,1)] if sign==1 else [(mp.mpf(1),-1),(1+h,1)])
    return score(al,hist,D)
def kstar(al,r,D,Q,h,H):return (Q*(D+h)-al*r*(D+H))/((al-1)*r*Q)
def Q0(z,sign):return limiting(alpha0,z,sign)[1]-alpha0*d0*z
def RR(z,sign,u,a):
    h,P,J=limiting(alpha0,z,sign)
    return 2*J+3*alpha0*d0*z*z/2-alpha0*a*z+u*(da_psi(alpha0,1+h)-d0*z)

def uniform_expansion():
    cases=[];worst=mp.mpf(0);worst_d2=mp.mpf(0);gap_count=0;mutant_error=mp.mpf(0)
    for u in map(mp.mpf,('-4','0','6')):
        for aa in map(mp.mpf,('-1','1.4','3')):
            for m in (256,1024):
                # n is integer; use its actual dimension offset in every law.
                n=int(mp.nint(d0*m*m+aa*m));D=m*n;a=(mp.mpf(n)-d0*m*m)/m
                al=alpha0+u/m;t=mp.mpf(2)/(m-1)
                values={};pred={0:mp.mpf(0)}
                for sign,z0 in zs.items():
                    fun=lambda z:m*D*(family(al,m,D,z,sign)-body(al,t))
                    for z in (z0,z0+mp.mpf('.13')):
                        residual=fun(z)-m*Q0(z,sign)-RR(z,sign,u,a)
                        d2=mp.diff(fun,z,2)-m*mp.diff(lambda q:Q0(q,sign),z,2)-mp.diff(lambda q:RR(q,sign,u,a),z,2)
                        worst=max(worst,m*abs(residual));worst_d2=max(worst_d2,m*abs(d2))
                        need(m*abs(residual)<10000 and m*abs(d2)<100000,'joint Taylor or derivative residual')
                    # Independent stationary solve, checked against the full
                    # compact endpoints/grid only as a finite diagnostic.
                    zm=mp.findroot(lambda z:mp.diff(fun,z),(z0-mp.mpf('.02'),z0+mp.mpf('.02')))
                    value=fun(zm);curv=mp.diff(fun,zm,2)
                    need(curv<0 and m*abs(zm-z0)<100,'continuous scalar localization')
                    lo=min(zs.values())/2;hi=2*max(zs.values())
                    need(all(fun(lo+(hi-lo)*j/16)<=value+mp.mpf('1e-240') for j in range(17)),'stationary point lost compact-grid diagnostic')
                    r,Q,h,H,g=data(al,m,zm,sign);kk=kstar(al,r,D,Q,h,H)
                    ranks=(int(mp.floor(kk)),int(mp.ceil(kk)))
                    need(m*(m-1)//2<=ranks[0]<=ranks[1]<=D-m*(m+1)//2,'physical rank counts')
                    integer=max(m*D*(family(al,m,D,zm,sign,k)-body(al,t)) for k in ranks)
                    need(0<=value-integer<mp.mpf('1e5')/m**4,'rank score rounding scale')
                    need(m*abs(value-alpha0*z0*(As[sign]+sigmas[sign]*u-a))<10000,'maximized affine score law')
                    values[sign]=value;pred[sign]=alpha0*z0*(As[sign]+sigmas[sign]*u-a)
                    cases.append({'u':fmt(u),'m':m,'n':n,'sign':sign,'m_z_displacement':fmt(m*(zm-z0)),
                                  'm4_rank_loss':fmt((value-integer)*m**4),'m_value_error':fmt(m*(value-pred[sign]))})
                selected=max({0:mp.mpf(0),**values},key=lambda s:({0:mp.mpf(0),**values})[s])
                ordered=sorted(pred,key=pred.get,reverse=True)
                if pred[ordered[0]]-pred[ordered[1]]>mp.mpf('.25'):
                    need(selected==ordered[0],'fixed gap family comparison');gap_count+=1
                wrong=max([mp.mpf(0)]+[alpha0*z*(As[s]-a) for s,z in zs.items()])
                mutant_error=max(mutant_error,abs(max(mp.mpf(0),*values.values())-wrong))
    need(mutant_error>mp.mpf('.1'),'omitting moving-order drift did not fail')
    return {'family_cases':len(cases),'max_m_Taylor_residual':fmt(worst),'max_m_second_derivative_residual':fmt(worst_d2),
            'fixed_gap_diagnostics':gap_count,'rows':cases,'rejected_mutation':'omit sigma_s*u drift',
            'scope':'scalar/rank finite diagnostics, not a global numerical quantum proof'}

def kernels_and_tails():
    tests=0;tails=0;max_quotient=mp.mpf(0);rows=[]
    for m in (256,1024):
        for u in map(mp.mpf,('-4','0','6')):
            al=alpha0+u/m
            for b in (mp.mpf('1e-100'),mp.mpf('.6'),1-mp.mpf('1e-180'),mp.mpf(1)):
                ratio_b=psi(al,1-b)/b**2;max_quotient=max(max_quotient,ratio_b)
                need(0<ratio_b<5,'negative endpoint kernel quotient');tests+=1
            D=m*int(mp.nint(d0*m*m));upper=D//2
            for sign,z in zs.items():
                r0,Q,h,H,g=data(al,m,z,sign);mass=abs(h)
                def base(r):
                    hist=[(1+r,upper),(mp.mpf(1),D-upper-2),(1+r/3,1),(1+2*r/3,1)]
                    return hist+([(1+r,-1),(1+r+mass,1)] if sign==1 else [(mp.mpf(1),-1),(1-mass,1)])
                for power in (10,70,140):
                    tau=mp.mpf(10)**(-power);r=r0-4*tau/m**2
                    old=base(r);changed=old[:]
                    for j in range(37):
                        mm=tau/37;v=1+r if j%2==0 else mp.mpf(1)
                        changed.extend([(v,-1),(v+mm if j%2==0 else v-mm,1)])
                    removed=D*(score(al,changed,D)-score(al,old,D))
                    gain=D*(score(al,base(r0),D)-score(al,old,D))
                    need(gain>removed,'moving-order relative tiny-tail improvement')
                    tails+=1
                rows.append({'m':m,'u':fmt(u),'sign':sign,'last_removed_per_mass':fmt(removed/tau),'last_gain_per_mass':fmt(gain/tau)})
    return {'endpoint_kernel_cases':tests,'max_kernel_quotient':fmt(max_quotient),'relative_tail_cases':tails,
            'smallest_removed_mass':'1e-140','precision_digits':mp.dps,'rows':rows,
            'scope':'entropy comparator algebra under localized body/root hypotheses; no assertion that every old perturbed spectrum is APPT'}

def unbounded_dimension_and_nonuniformity():
    m=1024;c=mp.mpf(4);r=mp.mpf(2)/(m-1)-c/m**2;t=mp.mpf(2)/(m-1)
    rows=[]
    for delta in map(mp.mpf,('.2','1e8','1e30')):
        n=int(mp.nint(delta*m*m));D=m*n;delta=mp.mpf(n)/m**2
        al=alpha0+mp.mpf(3)/m
        def integer_body(rr):
            Q=mp.expm1(al*mp.log1p(rr));k=kstar(al,rr,D,Q,0,0)
            return max(score(al,[(1+rr,j),(mp.mpf(1),D-j)],D) for j in (int(mp.floor(k)),int(mp.ceil(k))))
        penalty=D*(integer_body(t)-integer_body(r));lead=al*delta*c/2
        need(penalty>=lead*(1-mp.mpf(10)/m),'relative dimension coefficient lower bound')
        wrong_global_remainder=(lead-penalty)*m/(delta*c)
        need(wrong_global_remainder>mp.mpf('.1'),'discarding delta factor mutation not exposed')
        rows.append({'delta':fmt(delta),'relative_penalty_defect':fmt(wrong_global_remainder),
                     'absolute_defect':fmt(lead-penalty)})
    # An analytic spike demonstrates the logical failure of pointwise-to-
    # moving substitution. It is not an example about APPT itself.
    m=20
    spike=lambda al:mp.exp(-mp.mpf(m)**6*(al-alpha0-mp.mpf(1)/m)**2)
    need(spike(alpha0)<mp.mpf('1e-100') and abs(spike(alpha0+mp.mpf(1)/m)-1)<mp.mpf('1e-250'),
         'pointwise theorem is not moving-order uniformity')
    return {'actual_interval_state_dimension_cases':3,'rows':rows,
            'rejected_mutations':['absorb delta/m error into a dimension-independent 1/m error',
                                  'infer moving-order uniformity from a pointwise fixed-order theorem'],
            'scope':'actual interval-body states for dimension error; analytic spike only illustrates quantifier logic'}

save()
try:
    group('symbolic_joint_expansion',formal_expansion)
    group('whole_compact_scalar_and_ranks',uniform_expansion)
    group('moving_kernels_and_tiny_tails',kernels_and_tails)
    group('all_larger_dimension_coefficient',unbounded_dimension_and_nonuniformity)
    out['status']='PASS'
except BaseException as e:
    out['status']='FAIL';out['error']=str(e);out['traceback']=traceback.format_exc();print(out['traceback'],flush=True)
finally:
    out['ended_utc']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps({'status':out['status'],'run':str(RUN)}),flush=True)
if out['status']!='PASS':raise SystemExit(1)
