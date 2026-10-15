#!/usr/bin/env python3
"""Author controls for I0-I3; finite checks, not the whole quantum proof."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,traceback,sys
import sympy as sp
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for n in ('PAPER.md','THEOREM_MAP.md','checks.py'):(run/n).write_bytes((here/n).read_bytes())
record={'status':'RUNNING','author_only':True,'new_Lean':False,'full_APPT_enumeration':False,
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in run.iterdir()},'groups':{}}
def save():(run/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
def require(t,msg):
    if not t:raise AssertionError(msg)
def txt(x):return mp.nstr(x,35)
def group(n,f):
    print('START '+n,flush=True);record['groups'][n]=f();save();print('PASS '+n,flush=True)

def symbolic():
    D,Q,r,H,h,alpha=sp.symbols('D Q r H h alpha',positive=True)
    k=(Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)
    S=D+r*k+h;A=D+Q*k+H
    s=alpha*(Q-r)/((alpha-1)*Q);g=(r*H-Q*h)/(Q-r)
    require(sp.factor(S-s*D*(1-g/D))==0,'universal exact trace')
    require(sp.factor(Q*S-alpha*r*A)==0,'universal stationarity')
    L=sp.symbols('L',positive=True)
    k1=((L-r)*(D+h)-r*H)/r**2; S1=D+r*k1+h
    require(sp.factor(S1-(L/r)*D*(1-(r*H/L-h)/D))==0,'von Neumann exact trace')
    z=sp.symbols('z',positive=True)
    p=2*z/(z+2);P=p*p
    J=sp.factor((1+p/2)*2*p-p-P)
    a=sp.factor(2*J/(2*z)+3*P/4)
    require(J.subs(z,2)==1 and a.subs(z,2)==sp.Rational(5,4),'purity coefficient')
    phi=(1+sp.sqrt(5))/2; b=z/(1+z);v=sp.sqrt(1-b)
    P=(v-1)**2;dp=1-1/v
    J=-b*dp/2+b/4-P/4
    a=2*J/(z/2)+3*P
    require(sp.simplify(a.subs(z,phi)-(27-11*sp.sqrt(5))/2)==0,'half coefficient')
    return {'exact_checks':5,'purity_J':'1','purity_linear':'5/4',
            'half_linear':'(27-11sqrt(5))/2'}

mp.dps=220
def psi(alpha,y):
    if alpha==1:return y*mp.log(y)-y+1
    return (mp.expm1(alpha*mp.log(y))-alpha*(y-1))/(alpha-1)
def dpsi(alpha,y):
    if alpha==1:return mp.log(y)
    return alpha*mp.expm1((alpha-1)*mp.log(y))/(alpha-1)
def par(m,z,sign):
    r=mp.mpf(2)/(m-1+z);q=1+r
    mass=(2+r)*z/(z+2) if sign=='+' else -(2+r)*z/(2*(1+z))
    return r,q,mass
def raw_formula(alpha,m,D,z,sign):
    r,q,h=par(m,z,sign)
    if alpha==1:
        L=q*mp.log(q)
        H=(q+h)*mp.log(q+h)-q*mp.log(q) if sign=='+' else (1+h)*mp.log(1+h)
        k=((L-r)*(D+h)-r*H)/r**2
        S=D+r*k+h
        f=(k*L+H)/S-mp.log(S/D)
    else:
        Q=mp.expm1(alpha*mp.log(q))
        H=(q+h)**alpha-q**alpha if sign=='+' else mp.expm1(alpha*mp.log(1+h))
        k=(Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)
        A=D+Q*k+H;S=D+r*k+h
        f=(mp.log(A/D)-alpha*mp.log(S/D))/(alpha-1)
    return k,S,f
def body(alpha,r):
    q=1+r
    if alpha==1:
        s=q*mp.log(q)/r
        return s-1-mp.log(s)
    Q=mp.expm1(alpha*mp.log(q));s=alpha*(Q-r)/((alpha-1)*Q)
    return mp.log(Q/(alpha*r))/(alpha-1)-mp.log(s)
def gfun(alpha,m,z,sign):
    r,q,h=par(m,z,sign)
    if alpha==1:
        L=q*mp.log(q)
        H=(q+h)*mp.log(q+h)-q*mp.log(q) if sign=='+' else (1+h)*mp.log(1+h)
        return r*H/L-h
    Q=mp.expm1(alpha*mp.log(q))
    H=(q+h)**alpha-q**alpha if sign=='+' else mp.expm1(alpha*mp.log(1+h))
    return (r*H-Q*h)/(Q-r)
def crossing(alpha,m,z,sign):
    r,_,_=par(m,z,sign);t=mp.mpf(2)/(m-1)
    return gfun(alpha,m,z,sign)/(-m*mp.expm1(body(alpha,r)-body(alpha,t)))
def coeff(alpha,z,sign):
    h=2*z/(z+2) if sign=='+' else -z/(1+z)
    bp=mp.mpf(1) if sign=='+' else mp.mpf(0)
    P=psi(alpha,1+h);J=(bp+h/2)*dpsi(alpha,1+h)-alpha*(h+P)/2
    return P/(alpha*z),2*J/(alpha*z)+3*P/(2*alpha),J
orders=list(map(mp.mpf,('.1','.5','1','1.5','2','3','5')))+[1-mp.mpf('1e-25'),1+mp.mpf('1e-25')]

def universal_formula():
    cases=0; maxerr=mp.mpf(0); nearest1=0
    for alpha in orders:
        for m in (40,200,1000):
            D=m*max(m,int(mp.mpf('.2')*m*m))
            for z in map(mp.mpf,('.4','1','1.618','2','5')):
                for sign in ('+','-'):
                    r,q,h=par(m,z,sign);k,S,actual=raw_formula(alpha,m,D,z,sign)
                    g=gfun(alpha,m,z,sign)
                    formula=body(alpha,r)-mp.log1p(-g/D)
                    err=abs(actual-formula);maxerr=max(maxerr,err)
                    require(g>0 and g<D,'g outside physical normalized range')
                    require(err<mp.mpf('1e-155'),'exact real-rank formula mismatch')
                    n0=crossing(alpha,m,z,sign);D0=m*n0
                    _,_,f0=raw_formula(alpha,m,D0,z,sign)
                    require(abs(f0-body(alpha,mp.mpf(2)/(m-1)))<mp.mpf('1e-155'),'exact crossing formula mismatch')
                    deriv=mp.diff(lambda n:body(alpha,r)-mp.log1p(-g/(m*n)),mp.mpf(D)/m)
                    d0=-g/(m*(mp.mpf(D)/m)**2*(1-g/D))
                    require(abs(deriv-d0)<mp.mpf('1e-180'),'dimension derivative mismatch')
                    if alpha!=1 and abs(alpha-1)<mp.mpf('1e-24'):nearest1+=1
                    cases+=1
    # The opposite ratio is not a harmless entropy normalization convention.
    alpha=mp.mpf(2);r=mp.mpf('.02');q=1+r;Q=q*q-1
    s=alpha*(Q-r)/((alpha-1)*Q)
    wrong=mp.log(alpha*r/Q)/(alpha-1)-mp.log(s)
    require(abs(wrong-body(alpha,r))>mp.mpf('.01'),'reversed stationary ratio mutation not rejected')
    return {'full_formula_crossing_derivative_cases':cases,'near_one_cases':nearest1,
            'maximum_absolute_identity_error':txt(maxerr),'decimal_digits':mp.dps,
            'rejected_mutations':['reverse Q/(alpha r) in real optimum']}

def expansion_controls():
    cases=0;maxscaled=mp.mpf(0);max_gerror=mp.mpf(0)
    for alpha in orders:
        for z in map(mp.mpf,('.4','1','1.618','2','5')):
            for sign in ('+','-'):
                d,a,J=coeff(alpha,z,sign)
                residuals=[]
                for m in (500,2000,8000):
                    exact=crossing(alpha,m,z,sign);res=exact-d*m*m-a*m
                    require(abs(res)<mp.mpf('1e5'),'uniform bounded onset residual implausible')
                    residuals.append(res)
                    r,_,_=par(m,z,sign)
                    h0=2*z/(z+2) if sign=='+' else -z/(1+z)
                    g0=psi(alpha,1+h0)
                    gerr=abs((gfun(alpha,m,z,sign)-g0-J*r)/(r*r))
                    max_gerror=max(max_gerror,gerr);maxscaled=max(maxscaled,abs(res));cases+=1
                require(abs(residuals[-1]-residuals[-2])<max(mp.mpf('1'),abs(residuals[-2]))/50,
                        'linear expansion leaves a growing residual')
    alpha=mp.mpf(2);d,a,J=coeff(alpha,mp.mpf(2),'+')
    wrong=3*psi(alpha,2)/(2*alpha)
    require(a==mp.mpf('1.25') and wrong==mp.mpf('.75'),'omitted g derivative mutation')
    return {'expansion_cases':cases,'maximum_absolute_after_quadratic_linear':txt(maxscaled),
            'maximum_scaled_g_quadratic_residual':txt(max_gerror),
            'rejected_mutations':['omit contrast derivative J from linear onset']}

def golden(f,a,b,iterations=280):
    t=(mp.sqrt(5)-1)/2;x=b-t*(b-a);y=a+t*(b-a);fx=f(x);fy=f(y)
    for _ in range(iterations):
        if fx<fy:a=x;x=y;fx=fy;y=a+t*(b-a);fy=f(y)
        else:b=y;y=x;fy=fx;x=b-t*(b-a);fx=f(x)
    z=(a+b)/2;return z,f(z)
def multi_start(f,lo,hi):
    # Finite multi-start diagnostic: does not certify the general maxima.
    xs=[mp.e**(mp.log(lo)+(mp.log(hi)-mp.log(lo))*j/60) for j in range(61)]
    vals=[f(z) for z in xs];candidates=[(xs[0],vals[0]),(xs[-1],vals[-1])]
    for j in range(1,len(xs)-1):
        if vals[j]>=vals[j-1] and vals[j]>=vals[j+1]:candidates.append(golden(f,xs[j-1],xs[j+1]))
    return max(candidates,key=lambda p:p[1])
def scalar_diagnostics():
    rows=[];proofcases=0
    for alpha in map(mp.mpf,('.1','.5','1','1.5','2','3','5')):
        critical=[]
        for sign in ('+','-'):
            z,d=multi_start(lambda z:coeff(alpha,z,sign)[0],mp.mpf('.015'),mp.mpf(150))
            critical.append((d,z,sign,coeff(alpha,z,sign)[1]))
        critical.sort(reverse=True);d,z,s,a=critical[0]
        r0=min(c[1] for c in critical if abs(c[0]-d)<mp.mpf('1e-60'))
        r1=max(c[1] for c in critical if abs(c[0]-d)<mp.mpf('1e-60'))
        I=(r0/2,2*r1);samples=[]
        for m in (100,500,2000):
            both=[]
            for ss in ('+','-'):
                zz,value=multi_start(lambda v:crossing(alpha,m,v,ss),*I)
                both.append((value,zz,ss))
            value,zz,ss=max(both)
            samples.append({'m':m,'maximizing_sign':ss,'z':txt(zz),
                            'crossing_residual_after_linear':txt(value-d*m*m-a*m)})
            require(abs((value-d*m*m)/m-a)<mp.mpf('.7'),'full envelope linear diagnostic')
            proofcases+=1
        rows.append({'alpha':txt(alpha),'leading_sign':s,'d':txt(d),'critical_z':txt(z),'linear':txt(a),
                     'other_sign_d':txt(critical[1][0]),'samples':samples})
    require(next(row for row in rows if row['alpha']=='0.5')['leading_sign']=='-',
            'positive-only mutation misses half-order')
    require(next(row for row in rows if row['alpha']=='2.0')['leading_sign']=='+',
            'negative-only mutation misses purity')
    return {'whole_compact_two_sign_finite_diagnostics':proofcases,'rows':rows,
            'scope':'finite multistart search, not interval/global proof; analytic envelope argument in manuscript',
            'rejected_mutations':['positive-only for every alpha','negative-only for every alpha']}

save()
try:
    group('symbolic_exact_trace_and_cases',symbolic)
    group('all_fixed_order_trace_crossing',universal_formula)
    group('linear_onset_expansion',expansion_controls)
    group('two_sign_scalar_diagnostics',scalar_diagnostics)
    record['status']='PASS'
except BaseException as exc:
    record['status']='FAIL';record['exception']=str(exc);record['traceback']=traceback.format_exc()
    print(record['traceback'],flush=True)
finally:
    record['utc_end']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps({'status':record['status'],'run':str(run),'groups':list(record['groups'])}),flush=True)
if record['status']!='PASS':sys.exit(1)
