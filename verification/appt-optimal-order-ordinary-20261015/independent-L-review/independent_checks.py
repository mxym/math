#!/usr/bin/env python3
"""Independent L controls using the jointly regular kernel identities.
Finite controls do not optimize the full APPT set or certify all orders.
"""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,traceback
import sympy as sy
from mpmath import mp

ROOT=Path(__file__).resolve().parent
RUN=ROOT/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');RUN.mkdir(parents=True)
out={'status':'RUNNING','independent_of_author':True,'Lean':False,'full_quantum_optimization':False,'source':{},'groups':{}}
for p in sorted((ROOT/'snapshot').rglob('*')):
    if p.is_file():out['source'][str(p.relative_to(ROOT/'snapshot'))]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(p.read_text().splitlines())}
(RUN/'independent_checks.py').write_bytes(Path(__file__).read_bytes())
def save():(RUN/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(b,msg):
    if not b:raise AssertionError(msg)
def eq(a,b,msg):need(sy.simplify(a-b)==0,msg)
def group(name,fn):
    print('START '+name,flush=True);out['groups'][name]=fn();save();print('PASS '+name,flush=True)

def symbolic():
    a,r,w,h,DP=sy.symbols('alpha r w h DeltaPsi')
    Q=a*r+(a-1)*r*w;H=a*h+(a-1)*DP
    eq((r*H-Q*h)/(Q-r),(DP-h*w)/(1+w),'regular gain identity')
    eq(a*(Q-r)/((a-1)*Q),(1+w)/(1+(a-1)*w/a),'regular stationary trace ratio')
    L,Hlog=sy.symbols('L Hlog')
    eq((((Hlog-h)-h*w)/(1+w)).subs(w,(L-r)/r),r*Hlog/L-h,'vN gain continuation')
    v=(a-1)*w/a
    original=sy.log(1+v)/(a-1)-sy.log((1+w)/(1+v))
    regular=w*sy.log(1+v)/v-sy.log(1+w)
    # Log product identities hold on the small real neighborhood used here.
    eq(sy.diff(original,w),sy.diff(regular,w),'regular body derivative')
    eq(sy.limit(regular,a,1),w-sy.log(1+w),'vN body continuation')
    return {'exact_symbolic_checks':5,'scope':'removable kernel and normalized-trace identities'}

mp.dps=240
def fmt(x):return mp.nstr(x,36)
def exp2(x):
    if x==0:return mp.mpf('.5')
    if abs(x)>mp.mpf('.01'):return (mp.expm1(x)-x)/(x*x)
    term=mp.mpf('.5');total=term;k=0
    while True:
        k+=1;term*=x/(k+2);total+=term
        if abs(term)<mp.eps*max(1,abs(total)):return total
def ell(v):return mp.log1p(v)/v if v else mp.mpf(1)
def psi(a,y):
    if y==0:return mp.mpf(1)
    logy=mp.log(y);h=y-1;first=y*logy-h;delta=a-1
    return first+y*delta*logy**2*exp2(delta*logy)
def py(a,y):
    logy=mp.log(y);x=(a-1)*logy
    return a*logy*(mp.expm1(x)/x if x else 1)
def critF(a,x,sign):
    width=2 if sign==1 else 1;y=1+sign*x
    return x*(width-x)*sign*py(a,y)-width*psi(a,y)
def critical(a,sign):
    lo=mp.mpf('1e-15');hi=(2 if sign==1 else 1)-mp.mpf('1e-30')
    need(critF(a,lo,sign)>0 and critF(a,hi,sign)<0,'critical endpoint sign')
    for _ in range(500):
        x=(lo+hi)/2
        if critF(a,x,sign)>0:lo=x
        else:hi=x
    x=(lo+hi)/2;z=2*x/(2-x) if sign==1 else x/(1-x)
    return z,psi(a,1+sign*x)/(a*z)
def linear(a,z,sign):
    h=2*z/(z+2) if sign==1 else -z/(1+z)
    P=psi(a,1+h);J=((1 if sign==1 else 0)+h/2)*py(a,1+h)-a*(h+P)/2
    return 2*J/(a*z)+3*P/(2*a)
def setup():
    global alpha0,d0,zs,uc,ac,slopes,As
    p,b,alpha0=mp.findroot((lambda p,b,a:critF(a,p,1),lambda p,b,a:critF(a,b,-1),
            lambda p,b,a:psi(a,1+p)*(2-p)/(2*a*p)-psi(a,1-b)*(1-b)/(a*b)),
            (mp.mpf('.85'),mp.mpf('.61'),mp.mpf('.55')),tol=mp.mpf('1e-190'))
    zs={1:2*p/(2-p),-1:b/(1-b)};d0=psi(alpha0,1+p)/(alpha0*zs[1])
    As={s:linear(alpha0,z,s) for s,z in zs.items()}
    slopes={s:mp.diff(lambda a:psi(a,1+(2*z/(z+2) if s==1 else -z/(1+z)))/(a*z),alpha0) for s,z in zs.items()}
    need(slopes[1]>0>slopes[-1],'crossing slopes')
    uc=(As[-1]-As[1])/(slopes[1]-slopes[-1]);ac=As[1]+slopes[1]*uc
    return {'alpha0_illustration':fmt(alpha0),'d0_illustration':fmt(d0),'uc_illustration':fmt(uc),'ac_illustration':fmt(ac),'rigorous_interval_certificate':False}
def regular(a,r,z,sign):
    q=1+r;h=(2+r)*z/(z+2) if sign==1 else -(2+r)*z/(2*(1+z));base=q if sign==1 else mp.mpf(1)
    w=psi(a,q)/r;v=(a-1)*w/a
    B=w*ell(v)-mp.log1p(w);g=(psi(a,base+h)-psi(a,base)-h*w)/(1+w)
    stationary=(1+w)/(1+v)
    return h,g,B,stationary
def body(a,r):return regular(a,r,mp.mpf(1),1)[2]
def score(a,hist,D):
    S=mp.fsum(x*c for x,c in hist);s=S/D
    A=mp.fsum(psi(a,x/s)*c for x,c in hist)/D
    return A*ell((a-1)*A)
def family_score(a,m,n,z,sign):
    D=m*n;r=mp.mpf(2)/(m-1+z);h,g,B,st=regular(a,r,z,sign)
    kstar=(st*(D-g)-D-h)/r
    ranks=(int(mp.floor(kstar)),int(mp.ceil(kstar)))
    need(m*(m-1)//2<=ranks[0]<=ranks[1]<=D-m*(m+1)//2,'nonphysical rank')
    def at(k):
        hist=[(1+r,k),(mp.mpf(1),D-k)]+([(1+r,-1),(1+r+h,1)] if sign==1 else [(mp.mpf(1),-1),(1+h,1)])
        return score(a,hist,D)
    real=at(kstar);closed=B-mp.log1p(-g/D)
    need(abs(real-closed)<mp.mpf('1e-170'),'regular identity versus direct normalized kernel moment')
    integer=max(at(k) for k in ranks)
    need(0<=real-integer<10000* r*r/D**2,'integer rank loss')
    return integer,real-integer

def compact_barrier():
    orders=list(map(mp.mpf,('.12','.4','.8','1','2','8')))+[1-mp.mpf('1e-100'),1+mp.mpf('1e-100'),alpha0]
    data=[]
    for a in orders:
        both={s:critical(a,s) for s in (1,-1)};s=max(both,key=lambda x:both[x][1]);z,d=both[s]
        data.append((a,s,z,d,linear(a,z,s)))
    B0=10+max(abs(row[4]) for row in data);dmin=min(row[3] for row in data)
    m0=max(256,int(mp.ceil(4*(B0+2)/dmin)))
    rows=[]
    for a,s,z,d,aa in data:
        for m in (m0,4*m0):
            n=int(mp.floor(d*m*m-B0*m));need(n>=m,'lower-barrier dimension')
            actual,loss=family_score(a,m,n,z,s)
            real_bulk=body(a,mp.mpf(2)/(m-1))
            advantage=actual-real_bulk
            need(advantage>0,'actual integer state did not beat even continuous bulk')
            r=mp.mpf(2)/(m-1+z);h,g,Br,st=regular(a,r,z,s)
            cross=g/(-m*mp.expm1(Br-real_bulk))
            residual=cross-d*m*m-aa*m
            need(abs(residual)<10000,'joint compact crossing expansion')
            rows.append({'alpha':fmt(a),'m':m,'n':n,'sign':s,'m4_gain_over_real_bulk':fmt(m**4*advantage),
                         'm8_integer_loss':fmt(m**8*loss),'crossing_remainder':fmt(residual)})
    return {'actual_dimension_cases':len(rows),'shared_finite_test_B0':fmt(B0),'near_one_offset':'1e-100',
            'rows':rows,'scope':'finite actual one-family lower witnesses; no uniform-I cutoff or global M_I numerical certificate'}

def regularity_and_logic():
    cases=0
    for a in (mp.mpf(1),1-mp.mpf('1e-100'),1+mp.mpf('1e-100')):
        for r in map(mp.mpf,('.01','1e-7','1e-40')):
            for sign in (1,-1):
                z=mp.mpf('1.7');h,g,B,st=regular(a,r,z,sign)
                if a==1:
                    q=1+r;L=q*mp.log(q)
                    H=(q+h)*mp.log(q+h)-q*mp.log(q) if sign==1 else (1+h)*mp.log1p(h)
                    need(abs(g-(r*H/L-h))<mp.mpf('1e-180'),'direct vN gain')
                    need(abs(B-(L/r-1-mp.log(L/r)))<mp.mpf('1e-180'),'direct vN body')
                else:
                    # Extra working precision is solely for this independent
                    # raw-quotient cross-check, not the stable kernel helper.
                    with mp.workdps(480):
                        q=1+r;Q=mp.expm1(a*mp.log(q));H=(q+h)**a-q**a if sign==1 else (1+h)**a-1
                        rawg=(r*H-Q*h)/(Q-r)
                        rawB=mp.log(Q/(a*r))/(a-1)-mp.log(a*(Q-r)/((a-1)*Q))
                    need(abs(rawg-g)<mp.mpf('1e-140') and abs(rawB-B)<mp.mpf('1e-140'),'raw and regular identity near alpha1')
                cases+=1
    raw_division_failed=False
    try:
        a=mp.mpf(1);y=mp.mpf('.7')
        _=(y**a-1-a*(y-1))/(a-1)
    except ZeroDivisionError:
        raw_division_failed=True
    need(raw_division_failed,'raw quotient alpha=1 shortcut was not rejected')
    D=8;lam=[mp.mpf('.6'),mp.mpf('.4')]+[mp.mpf(0)]*6
    vn=mp.log(D)+mp.fsum(x*mp.log(x) for x in lam if x)
    for a in (1-mp.mpf('1e-80'),mp.mpf(1),1+mp.mpf('1e-80')):
        deficit=score(a,[(D*x,1) for x in lam],D)
        need(abs(deficit-vn)<mp.mpf('1e-78'),'singular density joint entropy continuity')
    # Exact symbolic cusp and two distinct integer minimizing points:
    x=sy.symbols('x');positive=sy.Rational(2,5);negative=-sy.Rational(3,5)
    for v in (sy.Rational(-3),sy.Rational(-1,2),sy.Rational(1,2),sy.Rational(4)):
        val=max(positive*v,negative*v)
        need(val>=min(positive,-negative)*abs(v),'sharp cusp gap inequality')
    Ntoy=lambda q:int(sy.ceiling(sy.Rational(3,10)+abs(q)))
    need(Ntoy(sy.Rational(1,4))==Ntoy(sy.Rational(-1,4))==1,'integer threshold need not have a unique minimizer')
    # A finite-prefix test cannot prove an infinite final tail condition.
    q=mp.mpf('1e-6');profit=lambda n:max(mp.mpf(0),q-mp.mpf(1)/n)
    need(all(profit(n)==0 for n in (1,10,1000,100000)) and profit(2000000)>0,'finite prefix versus all-later-n')
    return {'joint_alpha1_identity_cases':cases,'singular_density_continuity_cases':3,
            'rejected_shortcuts':['raw alpha-1 division at 1','unique continuous minimum implies unique integer minimizer',
                                  'a finite prefix certifies all-larger-n equality'],
            'scope':'identity/continuity and logical toy controls; toy examples are not APPT states'}

save()
try:
    group('symbolic_regular_identities',symbolic)
    group('independently_evaluated_constants',setup)
    group('compact_order_actual_lower_barrier',compact_barrier)
    group('joint_regularity_and_attainment_logic',regularity_and_logic)
    out['status']='PASS'
except BaseException as e:
    out.update(status='FAIL',error=str(e),traceback=traceback.format_exc());print(out['traceback'],flush=True)
finally:
    out['ended_utc']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps({'status':out['status'],'run':str(RUN)}),flush=True)
if out['status']!='PASS':raise SystemExit(1)
