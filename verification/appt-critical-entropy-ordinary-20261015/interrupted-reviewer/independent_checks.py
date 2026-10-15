#!/usr/bin/env python3
"""Independent finite diagnostics for frozen H0-H5. Not a formal certificate."""
from pathlib import Path
from datetime import datetime, timezone
from itertools import product
from fractions import Fraction as F
import hashlib, json, traceback
import sympy as s
from mpmath import mp

ROOT=Path(__file__).resolve().parent
INPUT=ROOT.parent/'entropy-review-input-v2'
RUN=ROOT/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True,exist_ok=False)
FILES=('PAPER.md','THEOREM_MAP.md','FOLLOWUP_TARGET.md','checks.py','AUTHOR_AUDIT.md','AUTHOR_AUDIT.json')
out={'status':'RUNNING','independent_agent':True,'Lean':False,
     'started_utc':datetime.now(timezone.utc).isoformat(),'frozen_input':{},'checks':{}}
for name in FILES:
    raw=(INPUT/name).read_bytes(); (RUN/name).write_bytes(raw)
    out['frozen_input'][name]={'sha256':hashlib.sha256(raw).hexdigest(),'lines':len(raw.decode().splitlines())}
(RUN/'independent_checks.py').write_bytes(Path(__file__).read_bytes())
def save():
    (RUN/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def check(ok,message):
    if not ok: raise AssertionError(message)
def eq(a,b,message): check(s.simplify(a-b)==0,message)
def fmt(v): return mp.nstr(v,35)
def group(name,fn):
    print('START '+name,flush=True); out['checks'][name]=fn(); save(); print('PASS '+name,flush=True)

def symbolic():
    m,z,r,D,k,h,H,Q,al=s.symbols('m z r D k h H Q alpha',positive=True)
    kap=2/(m-1+z); a=2+kap; p=a*z/(z+2); b=a*z/(2+2*z)
    eq(1-b,(m-1)/((m-1+z)*(1+z)),'negative endpoint')
    eq(kap*(m+2*p/(a-p)),a,'positive protection')
    eq(kap*(m+2*b/(a-2*b)),a,'negative diagonal protection')
    c=s.symbols('c'); rr=2/(m-1)-c/m**2
    for u,j in ((s.symbols('p'),1),(s.symbols('b'),2)):
        C=2*rr*m**2*u/((m-1)*(2+rr-j*u))
        target=1+2*u*(2-j*u)/((m-1)*(2+rr-j*u)**2)
        eq(s.diff(c-C,c),target,'cost root derivative')
    A=D+Q*k+H; S=D+r*k+h
    star=(Q*(D+h)-al*r*(D+H))/((al-1)*r*Q)
    f=(s.log(A/D)-al*s.log(S/D))/(al-1)
    eq(s.diff(f,k),r*Q*(star-k)/(A*S),'power rank derivative')
    L=s.symbols('L'); st1=((L-r)*(D+h)-r*H)/r**2
    eq(s.diff((k*L+H)/S-s.log(S/D),k),r**2*(st1-k)/S**2,'vN rank derivative')
    v,w,W=s.symbols('v w W',positive=True)
    # Derive half-order stationary value from direct moments, without the
    # manuscript's rank formula as an input.
    moment=D+(w-1)*k+v-1
    trace=D+(w*w-1)*k+v*v-1
    half=s.log(trace/D)-2*s.log(moment/D)
    stationary=s.solve(s.together(s.diff(half,k)),k)[0]
    trstar=s.factor(trace.subs(k,stationary))
    eq(trstar,w*D-(1-v)*(w-v),'half stationary trace')
    eq(moment.subs(k,stationary),2*trstar/(w+1),'half stationary moment')
    eq(1-(w+1)**2*W/(w*(W+1)**2),(W-w)*(w*W-1)/(w*(W+1)**2),'crossing rationalization')
    x=s.symbols('x'); P=50*x**3-50*x**2-141*x+159
    check(s.discriminant(P,x)==-7765800,'positive sign gap discriminant')
    vstar=(s.sqrt(5)-1)/2
    ratio=2*v*v*(1-v)/(1+v)
    eq(s.diff(ratio,v),-4*v*(v*v+v-1)/(1+v)**2,'negative critical derivative')
    eq(ratio.subs(v,vstar),5*s.sqrt(5)-11,'half critical constant')
    check(s.diff(ratio,v,2).subs(v,vstar).simplify()<0,'critical nondegeneracy')
    # Expansion directly in x=1/m, rather than epsilon=1/(m-1).
    B=lambda q:s.log((1+s.sqrt(1+q))**2/(4*s.sqrt(1+q)))
    bulkseries=s.series(B(r),r,0,5).removeO()
    eq(bulkseries,r*r/16-r**3/16+s.Rational(29,512)*r**4,'bulk Taylor')
    delta=s.series(bulkseries.subs(r,2*x/(1-x))-bulkseries.subs(r,2*x/(1+(z-1)*x)),x,0,5).removeO()
    eq(delta,z*x**3/2-3*z*z*x**4/4,'crossing expansion in 1/m')
    vv=s.symbols('vv',positive=True)
    wx=s.series(s.sqrt(1+2*x/(1+(z-1)*x)),x,0,2).removeO()
    vx=s.series(vv*s.sqrt((1-x)/(1+(z-1)*x)),x,0,2).removeO()
    gx=s.series((1-vx)*(wx-vx)/wx,x,0,2).removeO()
    eq(gx,(1-vv)**2+vv*(1-vv)*(1+z)*x,'gain expansion in 1/m')
    phi=(1+s.sqrt(5))/2
    d=2*(1-vstar)**2/phi
    linear=2*(1-vstar)/(phi*vstar)+3*(1-vstar)**2
    eq(d,5*s.sqrt(5)-11,'onset leading coefficient')
    eq(linear,(27-11*s.sqrt(5))/2,'onset linear coefficient')
    return {'identities_checked':17,'method':'independent differentiation, elimination and 1/m expansion',
            'positive_cubic_discriminant':-7765800,'half_linear':str(s.simplify(linear))}

def exact_physical():
    cases=0; witness=0; dense=0
    for m in (2,3,5):
        D=2*m*m; R=m*(m-1)//2; K=m*(m+1)//2
        for z in (F(1,3),F(7,4),F(9,2)):
            r=F(2,m-1+z); a=2+r
            for sign in (1,-1):
                u=a*z/(z+2) if sign==1 else a*z/(2*(1+z))
                for kind in (('edge',) if sign==1 else ('diagonal','edge')):
                    P=s.zeros(m)
                    if kind=='diagonal': P[0,0]=2*u
                    else: P[0,1]=P[1,0]=u
                    base=a*s.eye(m)-P
                    check(all(base[:j,:j].det()>0 for j in range(1,m+1)),'non-PD inverse base')
                    one=s.ones(m,1); invsum=(one.T*base.inv()*one)[0]
                    check(r*invsum<=1,'negative boundary not physical')
                    if sign==1 or kind=='diagonal': check(r*invsum==1,'wrong boundary equality')
                    else: check(r*invsum<1,'negative edge failed strict slack')
                    cases+=1
                # Direct adverse eigenvalue pairing for many Schmidt vectors,
                # including zeros and nonendpoint middle bodies.
                body=[1+r]*R+[1+r*F(j%4,3) for j in range(D-R-K)]+[F(1)]*K
                if sign==1: body[0]+=u
                else: body[-1]-=u
                raw=sorted(body,reverse=True)
                for coeff in product(range(3),repeat=m):
                    if not any(coeff): continue
                    weights=[F(v*v) for v in coeff]
                    for i in range(m):
                        for j in range(i+1,m): weights.extend([F(coeff[i]*coeff[j]),F(-coeff[i]*coeff[j])])
                    weights.extend([F(0)]*(D-m*m)); weights.sort()
                    check(sum(x*y for x,y in zip(raw,weights))>=0,'actual witness adverse trace is negative')
                    witness+=1
    for m in (4,7):
        a=F(103,50); one=s.ones(m,1)
        for sign in (1,-1):
            P0=s.zeros(m)
            if sign==1: P0[0,1]=P0[1,0]=F(4,5)
            else: P0[0,0]=F(6,5)
            for power in (5,70,150):
                tau=F(1,10**power); slots=[]
                for i in range(m):
                    for j in range(i+1,m):
                        if not(sign==1 and (i,j)==(0,1)): slots.append((i,j))
                    for j in range(i,m):
                        if not(sign==-1 and (i,j)==(0,0)): slots.append((i,j))
                P=P0.copy(); mass=tau/len(slots)
                for i,j in slots:
                    if i==j:P[i,i]+=2*mass
                    else:P[i,j]+=mass; P[j,i]+=mass
                A=a*s.eye(m)-P
                check(all(A[:j,:j].det()>0 for j in range(1,m+1)),'dense full-slot base singular')
                inc=(one.T*(A.inv()-(a*s.eye(m)-P0).inv())*one)[0]
                check(inc>=2*tau/a**2,'walk lower bound loses some rest mass')
                dense+=1
    return {'exact_PSD_pattern_cases':cases,'direct_Schmidt_pairings':witness,
            'dense_full_slot_cases':dense,'smallest_exact_mass':'1e-150',
            'scope':'finite physical/algebraic controls; all-unitary proof remains analytic'}

mp.dps=380
def score(alpha,hist,D):
    trace=mp.fsum(x*n for x,n in hist)
    if alpha==1: return mp.fsum(x*mp.log(x)*n for x,n in hist)/trace-mp.log(trace/D)
    moment=mp.fsum(x**alpha*n for x,n in hist)
    return (mp.log(moment/D)-alpha*mp.log(trace/D))/(alpha-1)
def family(alpha,m,D,z,sign,k):
    r=mp.mpf(2)/(m-1+z); q=1+r; a=2+r
    u=a*z/(z+2) if sign==1 else a*z/(2*(1+z))
    hist=[(q,k),(mp.mpf(1),D-k)]
    hist += [(q,-1),(q+u,1)] if sign==1 else [(mp.mpf(1),-1),(1-u,1)]
    return score(alpha,hist,D)
def rank_star(alpha,m,D,z,sign):
    r=mp.mpf(2)/(m-1+z); q=1+r; a=2+r
    u=a*z/(z+2) if sign==1 else a*z/(2*(1+z)); h=sign*u
    if alpha==1:
        L=q*mp.log(q); H=(q+u)*mp.log(q+u)-L if sign==1 else (1-u)*mp.log(1-u)
        return ((L-r)*(D+h)-r*H)/(r*r)
    Q=mp.expm1(alpha*mp.log(q)); H=(q+u)**alpha-q**alpha if sign==1 else (1-u)**alpha-1
    return (Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)

def entropy_controls():
    enumeration=0; tailcases=0; details=[]
    for al in map(mp.mpf,('.01','.5','1','1.0001','2','10')):
        m=4; D=128; R=6; K=10
        for z in map(mp.mpf,('.2','1.7','8')):
            for sign in (1,-1):
                star=rank_star(al,m,D,z,sign)
                adj={max(R,min(D-K,int(fun(star)))) for fun in (mp.floor,mp.ceil)}
                best=max(family(al,m,D,z,sign,k) for k in adj)
                check(all(family(al,m,D,z,sign,k)<=best+mp.mpf('1e-340') for k in range(R,D-K+1)),'rank formula omits a finite-family winner')
                enumeration+=1
    # Same-body tail subtraction: orders near one and tiny tails, retaining
    # two signs and nonendpoint coordinates. These are algebraic tests under
    # the proven variance/cost hypotheses, not an APPT feasible-set search.
    orders=list(map(mp.mpf,('.01','.5','1','2','10')))+[1-mp.mpf('1e-30'),1+mp.mpf('1e-30')]
    for al in orders:
        m=1200; n=300000; D=m*n
        for sign in (1,-1):
            z=mp.mpf('1.8'); r0=mp.mpf(2)/(m-1+z); a=2+r0
            u=a*z/(z+2) if sign==1 else a*z/(2*(1+z))
            body=[(mp.mpf(1),D//2),(mp.mpf(0),D-D//2-2),(mp.mpf(1)/3,1),(mp.mpf(2)/3,1)]
            def head(r):
                hist=[(1+r*t,ct) for t,ct in body]
                return hist+([(1+r,-1),(1+r+u,1)] if sign==1 else [(mp.mpf(1),-1),(1-u,1)])
            ratios=[]
            for exponent in (10,80,160):
                tau=mp.mpf(10)**-exponent; r=r0-4*tau/m**2
                base=head(r); changed=base[:]
                for j in range(31):
                    mass=tau/31; old=1+r if j%2==0 else mp.mpf(1)
                    changed.extend([(old,-1),(old+mass if j%2==0 else old-mass,1)])
                removed=D*(score(al,changed,D)-score(al,base,D))
                gained=D*(score(al,head(r0),D)-score(al,base,D))
                check(gained>removed,'tiny-tail exact comparator not improving')
                derivative=mp.diff(lambda q:score(al,head(q),D),r)
                check(derivative>=al*r/8,'localized derivative too small')
                ratios.append(removed/tau); tailcases+=1
            check(abs(ratios[1]-ratios[2])<mp.mpf('1e-65'),'subtraction failed uniform linear scaling into tiny tails')
            details.append({'alpha':fmt(al),'sign':sign,'removed_per_mass':fmt(ratios[-1])})
    return {'finite_integer_enumerations':enumeration,'tiny_tail_cases':tailcases,
            'precision_decimal_digits':mp.dps,'smallest_mass':'1e-160','linear_scaling':details}

def onset_controls():
    phi=(1+mp.sqrt(5))/2; ds=5*mp.sqrt(5)-11; aa=(27-11*mp.sqrt(5))/2
    def nu(m,z):
        L=mp.mpf(m-1); w=mp.sqrt(1+2/(L+z)); W=mp.sqrt(1+2/L)
        v=mp.sqrt(L/((L+z)*(1+z)))
        return (1-v)*(w-v)*(W+1)**2/(m*(W-w)*(w*W-1))
    rows=[]
    for m in (60,300,1500):
        zm=mp.findroot(lambda z:mp.diff(lambda y:nu(m,y),z),(phi,phi+mp.mpf(5)/m))
        N=nu(m,zm)
        check(phi/2<zm<2*phi,'stationary crossing out of full compact interval')
        # Full-interval finite grid is an independent control only.
        check(all(nu(m,phi/2+(2*phi-phi/2)*j/80)<=N+mp.mpf('1e-300') for j in range(81)),'stationary scalar maximum loses to compact-grid point')
        residual=N-ds*m*m-aa*m
        check(abs(residual)<10,'linear onset formula residual unbounded in tested range')
        r=mp.mpf(2)/(m-1); W=mp.sqrt(1+r); Breal=mp.log((W+1)**2/(4*W))
        margins=[]; losses=[]
        for n in (int(mp.floor(N)),int(mp.ceil(N))):
            D=m*n; kb=mp.mpf(D)/(W+1)
            Bint=max(score(mp.mpf('.5'),[(1+r,k),(mp.mpf(1),D-k)],D) for k in (int(mp.floor(kb)),int(mp.ceil(kb))))
            ks=rank_star(mp.mpf('.5'),m,D,zm,-1)
            real=family(mp.mpf('.5'),m,D,zm,-1,ks)
            fint=max(family(mp.mpf('.5'),m,D,zm,-1,k) for k in (int(mp.floor(ks)),int(mp.ceil(ks))))
            check(0<=Breal-Bint<10/mp.mpf(m)**8,'bulk integer loss scale')
            check(0<=real-fint<10/mp.mpf(m)**8,'head integer loss scale')
            check((fint-Bint)>0 if n<N else (fint-Bint)<0,'actual integer-rank crossing mismatch')
            margins.append({'n':n,'m5_margin':fmt((fint-Bint)*m**5)})
            losses.append({'m8_bulk_loss':fmt((Breal-Bint)*m**8),'m8_head_loss':fmt((real-fint)*m**8)})
        D=m*N; ks=rank_star(mp.mpf('.5'),m,D,zm,-1)
        check(abs(family(mp.mpf('.5'),m,D,zm,-1,ks)-Breal)<mp.mpf('1e-320'),'exact real crossing fails direct entropy')
        slope=mp.diff(lambda n:family(mp.mpf('.5'),m,m*n,zm,-1,rank_star(mp.mpf('.5'),m,m*n,zm,-1))-Breal,N)
        check(slope<0,'onset profit slope sign')
        rows.append({'m':m,'z':fmt(zm),'envelope':fmt(N),'quadratic_linear_residual':fmt(residual),'m5_slope':fmt(slope*m**5),'actual_rank_margins':margins,'rounding_losses':losses})
    return {'scalar_cases':3,'actual_dimension_cases':6,'precision_decimal_digits':mp.dps,'cases':rows,
            'scope':'finite scalar/rank controls; no global numerical or Diophantine certificate'}

save()
try:
    group('symbolic_derivation',symbolic)
    group('exact_physical_and_full_slot_walks',exact_physical)
    group('entropy_ranks_and_relative_tails',entropy_controls)
    group('half_order_onset_and_two_rounding_errors',onset_controls)
    out['status']='PASS'
except BaseException as exc:
    out['status']='FAIL'; out['exception']=str(exc); out['traceback']=traceback.format_exc(); print(out['traceback'],flush=True)
finally:
    out['ended_utc']=datetime.now(timezone.utc).isoformat(); save()
    print(json.dumps({'status':out['status'],'run':str(RUN)}),flush=True)
if out['status']!='PASS': raise SystemExit(1)
