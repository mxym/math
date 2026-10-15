#!/usr/bin/env python3
"""Author calculus/phase controls, not a numerical proof of J0-J3."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,traceback,sys
import sympy as sp
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for name in ('PAPER.md','THEOREM_MAP.md','checks.py'):(run/name).write_bytes((here/name).read_bytes())
out={'status':'RUNNING','author_only':True,'new_Lean':False,
     'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in run.iterdir()},'groups':{}}
def save():(run/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(t,m):
    if not t:raise AssertionError(m)
def group(n,f):
    print('START '+n,flush=True);out['groups'][n]=f();save();print('PASS '+n,flush=True)

def symbolic():
    p,b,alpha=sp.symbols('p b alpha',positive=True)
    for arg,var,width,denom in ((1+p,p,2,2),(1-b,b,1,1)):
        f=(arg**alpha-1-alpha*(arg-1))/(alpha-1)
        ratio=(width-var)*f/(denom*alpha*var)
        F=var*(width-var)*sp.diff(f,var)-width*f
        G=(width-var)*sp.diff(f,var,2)-2*sp.diff(f,var)
        need(sp.simplify(sp.diff(ratio,var)-F/(denom*alpha*var**2))==0,'ratio numerator')
        need(sp.simplify(sp.diff(F,var)-var*G)==0,'F derivative')
        expected=(alpha*(1+p)**(alpha-3)*(2*alpha-7-(alpha+1)*p)
                  if var==p else -alpha*(alpha+1)*(1-b)**(alpha-2))
        need(sp.simplify(sp.diff(G,var)-expected)==0,'G derivative')
        f1=arg*sp.log(arg)-arg+1
        G1=(width-var)*sp.diff(f1,var,2)-2*sp.diff(f1,var)
        need(sp.simplify(sp.diff(G1,var)-expected.subs(alpha,1))==0,'von Neumann derivative')
    need(sp.Rational(31,162)>sp.Rational(3,16),'rational separation')
    need(sp.Rational(179,80)**2>5,'sqrt5 separation')
    need(sp.Rational(56,81)-sp.Rational(1,2)==sp.Rational(31,162),'log2 lower')
    need((2*sp.Integer(10)-7)>0,'all-alpha G decreasing false variant')
    return {'exact_identities':11,'rejected_mutations':['G_positive decreasing for every alpha'],
            'scope':'derivative identities and rational separations; global root count is analytic proof'}

mp.dps=95
def psi(alpha,y):
    if alpha==1:return y*mp.log(y)-y+1
    return (mp.expm1(alpha*mp.log(y))-alpha*(y-1))/(alpha-1)
def dp(alpha,y):
    if alpha==1:return mp.log(y)
    return alpha*mp.expm1((alpha-1)*mp.log(y))/(alpha-1)
def crit(alpha,sign):
    width=mp.mpf(2) if sign=='+' else mp.mpf(1)
    def F(x):
        y=1+x if sign=='+' else 1-x
        f=psi(alpha,y);df=dp(alpha,y) if sign=='+' else -dp(alpha,y)
        return x*(width-x)*df-width*f
    lo=mp.mpf('1e-12');hi=width-mp.mpf('1e-20')
    need(F(lo)>0 and F(hi)<0,'critical bisection endpoint signs')
    for _ in range(185):
        mid=(lo+hi)/2
        if F(mid)>0:lo=mid
        else:hi=mid
    x=(lo+hi)/2;y=1+x if sign=='+' else 1-x
    f=psi(alpha,y);df=dp(alpha,y) if sign=='+' else -dp(alpha,y)
    G=(width-x)*alpha*y**(alpha-2)-2*df
    curvature=G/((2 if sign=='+' else 1)*alpha*x)
    value=(width-x)*f/((2 if sign=='+' else 1)*alpha*x)
    return x,value,curvature
def calculus_controls():
    rows=[];last=None
    for alpha in map(mp.mpf,('.001','.01','.1','.5','1','2','3.5','4','10','50','100')):
        p,Dp,cp=crit(alpha,'+');b,Dm,cm=crit(alpha,'-')
        need(cp<0 and cm<0,'nonnegative critical curvature')
        if last:need(Dp>last[0] and Dm<last[1],'strict order monotonicity')
        slopep=p*(2-p)/2*mp.quad(lambda u:(1-u)*(1+u*p)**(alpha-2)*mp.log(1+u*p),[0,1])
        slopem=b*(1-b)*mp.quad(lambda u:(1-u)*(1-u*b)**(alpha-2)*mp.log(1-u*b),[0,1])
        need(slopep>0 and slopem<0,'strict envelope derivative sign')
        rows.append({'alpha':str(alpha),'p':mp.nstr(p,27),'b':mp.nstr(b,27),
                     'D_positive':mp.nstr(Dp,27),'D_negative':mp.nstr(Dm,27),
                     'positive_curvature':mp.nstr(cp,27),'negative_curvature':mp.nstr(cm,27)})
        last=(Dp,Dm)
    return {'fixed_order_two_sign_critical_cases':len(rows)*2,'rows':rows,
            'scope':'finite critical-point and integral-slope controls; uniqueness comes from written F/G proof'}
def transition_controls():
    lo=mp.mpf('.5');hi=mp.mpf(1)
    for _ in range(100):
        mid=(lo+hi)/2
        if crit(mid,'+')[1]>crit(mid,'-')[1]:hi=mid
        else:lo=mid
    ax=(lo+hi)/2;p,Dp,cp=crit(ax,'+');b,Dm,cm=crit(ax,'-')
    need(mp.mpf('.5')<ax<1,'transition outside proved interval')
    need(abs(Dp-Dm)<mp.mpf('1e-30'),'numeric sign tie not located')
    # I's critical coefficients retain both signs at this leading tie.
    def coefficient(z,sign):
        h=2*z/(z+2) if sign=='+' else -z/(1+z)
        P=psi(ax,1+h);J=((1 if sign=='+' else 0)+h/2)*dp(ax,1+h)-ax*(h+P)/2
        return 2*J/(ax*z)+3*P/(2*ax)
    zp=2*p/(2-p);zm=b/(1-b)
    return {'alpha_crossing_approximation':mp.nstr(ax,31),'d_min_approximation':mp.nstr((Dp+Dm)/2,31),
            'positive_critical_z':mp.nstr(zp,31),'negative_critical_z':mp.nstr(zm,31),
            'positive_linear_at_numeric_crossing':mp.nstr(coefficient(zp,'+'),31),
            'negative_linear_at_numeric_crossing':mp.nstr(coefficient(zm,'-'),31),
            'numeric_bracket_width':mp.nstr(hi-lo,8),
            'scope':'illustrative high precision, not a rigorous interval certificate or an algebraic definition'}

save()
try:
    group('exact_F_G_identities',symbolic)
    group('every_order_critical_control',calculus_controls)
    group('unique_order_transition_diagnostic',transition_controls)
    out['status']='PASS'
except BaseException as e:
    out['status']='FAIL';out['error']=str(e);out['traceback']=traceback.format_exc();print(out['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':out['status'],'run':str(run)}),flush=True)
if out['status']!='PASS':sys.exit(1)
