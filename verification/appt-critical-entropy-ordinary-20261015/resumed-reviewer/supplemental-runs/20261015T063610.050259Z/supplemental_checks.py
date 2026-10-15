#!/usr/bin/env python3
"""Fresh resume-reviewer diagnostics. Mathematical coverage is in the reports.

These finite diagnostics do not test the entire APPT feasible set. The older
reviewer's script is separately rerun, with its original authorship preserved.
"""
from pathlib import Path
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib, json, traceback
import sympy as sy
from mpmath import mp

ROOT=Path(__file__).resolve().parent
RUN=ROOT/'supplemental-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN.mkdir(parents=True)
report={'status':'RUNNING','Lean':False,'independent_of_author':True,
        'written_by':'resumed independent review agent',
        'source':{},'checks':{},'started_utc':datetime.now(timezone.utc).isoformat()}
for p in sorted((ROOT/'snapshot').rglob('*')):
    if p.is_file():
        report['source'][str(p.relative_to(ROOT/'snapshot'))]={
            'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
            'lines':len(p.read_text().splitlines())}
(RUN/'supplemental_checks.py').write_bytes(Path(__file__).read_bytes())

def require(b,msg):
    if not b: raise AssertionError(msg)
def exact(a,b,msg): require(sy.simplify(a-b)==0,msg)
def save(): (RUN/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
def group(name,fn):
    print('START '+name,flush=True)
    report['checks'][name]=fn(); save(); print('PASS '+name,flush=True)

def symbolic():
    al,Q,r,D,h,H,k,L=sy.symbols('alpha Q r D h H k L', nonzero=True)
    S=D+r*k+h; A=D+Q*k+H
    # Eliminate k from the stationarity equation, rather than assume g.
    k0=sy.solve(Q*S-al*r*A,k)[0]
    S0=sy.factor(S.subs(k,k0))
    s=al*(Q-r)/((al-1)*Q)
    g=(r*H-Q*h)/(Q-r)
    exact(S0,s*(D-g),'general exact stationary trace')
    exact(A.subs(k,k0),Q*S0/(al*r),'stationary moment ratio')
    k1=sy.solve((L-r)*(D+h)-r*H-r*r*k,k)[0]
    exact(S.subs(k,k1),L/r*(D-(r*H/L-h)),'vN stationary trace')
    # Generic first-order g coefficient: all scalar powers encoded by their
    # exact values and first derivatives at the positive limiting raw head.
    mass,P,Pp,b=sy.symbols('mass P Pprime baseprime')
    Qser=al*r+al*(al-1)*r*r/2+al*(al-1)*(al-2)*r**3/6
    H0=al*mass+(al-1)*P
    H1=(al-1)*Pp*(b+mass/2)+al*mass/2
    finiteh=mass*(1+r/2)
    gs=(r*(H0+r*H1)-Qser*finiteh)/(Qser-r)
    J=(b+mass/2)*Pp-al*mass/2-al*P/2
    exact(sy.limit(gs,r,0),P,'generic gain leading coefficient')
    exact(sy.limit((gs-P)/r,r,0),J,'generic gain linear coefficient')
    # Its vN analogue uses a direct log-moment derivative.
    Lv=r+r*r/2-r**3/6
    H01=mass+P; H11=Pp*(b+mass/2)+mass/2
    g1=r*(H01+r*H11)/Lv-finiteh
    exact(sy.limit((g1-P)/r,r,0),J.subs(al,1),'vN gain linear coefficient')
    nu,gg,m,n=sy.symbols('nu g m n',positive=True)
    exact(sy.diff(-sy.log(1-gg/(m*n)),n),-gg/(m*n*n*(1-gg/(m*n))),'dimension slope')
    return {'exact_identities':7,'scope':'trace, head gain coefficients and n derivative; no formal certificate'}

mp.dps=250
def fstr(v): return mp.nstr(v,35)
def psi(al,y):
    return y*mp.log(y)-y+1 if al==1 else (y**al-1-al*(y-1))/(al-1)
def psip(al,y):
    return mp.log(y) if al==1 else al*(y**(al-1)-1)/(al-1)
def score(al,hist,D):
    S=mp.fsum(v*c for v,c in hist)
    if al==1:return mp.fsum(v*mp.log(v)*c for v,c in hist)/S-mp.log(S/D)
    return (mp.log(mp.fsum(v**al*c for v,c in hist)/D)-al*mp.log(S/D))/(al-1)
def ingredients(al,r,z,sign):
    q=1+r
    h=2*z/(z+2) if sign==1 else -z/(1+z)
    hp=h*(1+r/2)
    if al==1:
        L=q*mp.log(q)
        H=(q+hp)*mp.log(q+hp)-L if sign==1 else (1+hp)*mp.log(1+hp)
        g=r*H/L-hp
        B=L/r-1-mp.log(L/r)
    else:
        Q=mp.expm1(al*mp.log(q))
        H=(q+hp)**al-q**al if sign==1 else (1+hp)**al-1
        g=(r*H-Q*hp)/(Q-r)
        s=al*(Q-r)/((al-1)*Q)
        B=mp.log(Q/(al*r))/(al-1)-mp.log(s)
    return h,hp,H,g,B
def star(al,r,D,h,H):
    q=1+r
    if al==1:
        L=q*mp.log(q); return ((L-r)*(D+h)-r*H)/(r*r)
    Q=mp.expm1(al*mp.log(q))
    return (Q*(D+h)-al*r*(D+H))/((al-1)*r*Q)
def hist(r,D,h,k,sign):
    q=1+r
    return [(q,k),(mp.mpf(1),D-k)]+([(q,-1),(q+h,1)] if sign==1 else [(mp.mpf(1),-1),(1+h,1)])

def general_onset():
    exactcases=0; expansioncases=0; rows=[]; worst=mp.mpf(0)
    orders=list(map(mp.mpf,('.17','.5','.9999','1','1.0001','2','7')))
    orders += [1-mp.mpf('1e-35'),1+mp.mpf('1e-35')]
    for al in orders:
        for sign in (1,-1):
            for z in map(mp.mpf,('.5','1.7','4')):
                r=mp.mpf('0.003'); D=mp.mpf(10)**7
                h,hp,H,g,B=ingredients(al,r,z,sign)
                k=star(al,r,D,hp,H)
                direct=score(al,hist(r,D,hp,k,sign),D)
                exactvalue=B-mp.log1p(-g/D)
                require(abs(direct-exactvalue)<mp.mpf('1e-180'),'generic normalized stationary formula')
                require(g>0,'signed gain not positive')
                kbulk=star(al,r,D,mp.mpf(0),mp.mpf(0))
                require(abs(score(al,[(1+r,kbulk),(mp.mpf(1),D-kbulk)],D)-B)<mp.mpf('1e-180'),'head-free real envelope')
                J=((1 if sign==1 else 0)+h/2)*psip(al,1+h)-al*h/2-al*psi(al,1+h)/2
                rp=mp.mpf('1e-15')
                gp=ingredients(al,rp,z,sign)[3]
                scaled=(gp-psi(al,1+h)-J*rp)/rp**2
                require(abs(scaled)<10000,'generic gain coefficient residual')
                exactcases+=1
                d=psi(al,1+h)/(al*z)
                aa=2*J/(al*z)+3*psi(al,1+h)/(2*al)
                residuals=[]
                for dim in (10000,20000):
                    t=mp.mpf(2)/(dim-1); rr=mp.mpf(2)/(dim-1+z)
                    gg=ingredients(al,rr,z,sign)[3]
                    BB=ingredients(al,t,z,sign)[4]
                    Br=ingredients(al,rr,z,sign)[4]
                    cross=gg/(dim*(-mp.expm1(Br-BB)))
                    residual=cross-d*dim*dim-aa*dim
                    require(abs(residual)<10000,'uniform crossing expansion residual')
                    residuals.append(residual); expansioncases+=1
                    worst=max(worst,abs(residual))
                require(abs(residuals[1]-residuals[0])<mp.mpf('.1'),'crossing O(1) residual consistency')
                rows.append({'alpha':fstr(al),'sign':sign,'z':fstr(z),'gain_J':fstr(J),
                             'a':fstr(aa),'crossing_residuals':[fstr(v) for v in residuals]})
    return {'precision_digits':mp.dps,'stationary_cases':exactcases,'expansion_cases':expansioncases,
            'max_abs_crossing_residual':fstr(worst),'cases':rows,
            'scope':'finite algebraic/scalar controls; no actual all-matrix optimization'}

def adverse_variants():
    rejected=[]
    # Raw convex coefficients do not normalize correctly unless trace-weighted.
    vertices=[[F(1),F(1),F(1)],[F(1),F(2),F(1)]]
    w=[F(1,3),F(2,3)]
    raw=[sum(w[j]*vertices[j][i] for j in range(2)) for i in range(3)]
    current=[a/sum(raw) for a in raw]
    bad=[sum(w[j]*vertices[j][i]/sum(vertices[j]) for j in range(2)) for i in range(3)]
    good=[sum(w[j]*vertices[j][i]/sum(raw) for j in range(2)) for i in range(3)]
    require(good==current and bad!=current,'trace-weighted mutation must fail')
    rejected.append('unweighted raw-to-normalized cube coefficients')
    al=mp.mpf(2); r=mp.mpf('.01'); D=10000
    def flat(rr):
        b=1+rr/2
        return score(al,[(b,D-1),(b+1,1)],D)
    require(mp.diff(flat,r)<0,'flat body must reject unconditional positive contrast derivative')
    rejected.append('contrast derivative positive without C4 variance localization')
    # The stationary moment ratio in B is Q/(alpha*r), not its reciprocal.
    z=mp.mpf('1.7'); h,hp,H,g,B=ingredients(al,r,z,1)
    Q=mp.expm1(al*mp.log1p(r)); sa=al*(Q-r)/((al-1)*Q)
    wrong=mp.log(al*r/Q)/(al-1)-mp.log(sa)
    require(abs(wrong-B)>mp.mpf('.001'),'reciprocal B constant mutation must fail')
    rejected.append('reciprocal stationary moment constant')
    # Negative head has negative trace increment. The correct general formula
    # is compared to direct moments; replacing the trace by +beta changes it.
    al=mp.mpf('.5'); h,hp,H,g,B=ingredients(al,r,z,-1)
    k=star(al,r,D,hp,H); hv=hist(r,D,hp,k,-1)
    right=score(al,hv,D)
    moment=mp.fsum(v**al*c for v,c in hv)
    wrongtrace=D+r*k-hp
    wrong=(mp.log(moment/D)-al*mp.log(wrongtrace/D))/(al-1)
    require(abs(wrong-right)>mp.mpf('1e-6'),'negative trace sign mutation must fail')
    rejected.append('positive trace increment for negative anomaly')
    # Compact perturbation can choose different critical ties without a rate
    # of convergence: a genuine a=max over ties is required, not an average.
    d1,d2,a1,a2=F(1),F(1),F(-1),F(3)
    for m in (100,1000):
        require(max(d1*m*m+a1*m,d2*m*m+a2*m)==m*m+a2*m,'all critical ties in next coefficient')
    rejected.append('average linear coefficient across critical ties')
    return {'wrong_variants_rejected':rejected,'actual_failures':'Any unexpected assertion failure remains in this run RESULT.json.'}

save()
try:
    group('symbolic_elimination_and_gain_coefficients',symbolic)
    group('general_order_exact_trace_and_crossings',general_onset)
    group('adversarial_mutations',adverse_variants)
    report['status']='PASS'
except BaseException as exc:
    report['status']='FAIL'; report['exception']=str(exc)
    report['traceback']=traceback.format_exc(); print(report['traceback'],flush=True)
finally:
    report['ended_utc']=datetime.now(timezone.utc).isoformat(); save()
    print(json.dumps({'status':report['status'],'run':str(RUN)}),flush=True)
if report['status']!='PASS': raise SystemExit(1)
