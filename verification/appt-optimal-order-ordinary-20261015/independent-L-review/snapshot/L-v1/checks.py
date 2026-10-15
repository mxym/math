#!/usr/bin/env python3
"""Finite actual-state and continuous-envelope diagnostics for L0-L2."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,traceback
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
for n in ['PAPER.md','THEOREM_MAP.md','checks.py']:
    (run/n).write_bytes((here/n).read_bytes())
out={'status':'RUNNING','author_only':True,'new_Lean':False,
     'not_full_quantum_feasible_set_enumeration':True,
     'source_sha256':{n:hashlib.sha256((run/n).read_bytes()).hexdigest()
                      for n in ['PAPER.md','THEOREM_MAP.md','checks.py']},'groups':{}}
def save(): (run/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(t,msg):
    if not t: raise AssertionError(msg)
def st(x): return mp.nstr(x,30)
mp.dps=90
def psi(a,y):
    if a==1:return y*mp.log(y)-y+1
    return (mp.expm1(a*mp.log(y))-a*(y-1))/(a-1)
def py(a,y):
    if a==1:return mp.log(y)
    return a*mp.expm1((a-1)*mp.log(y))/(a-1)
def crit_equation(a,x,s):
    w=mp.mpf(2) if s=='+' else mp.mpf(1)
    y=1+x if s=='+' else 1-x
    return x*(w-x)*(py(a,y) if s=='+' else -py(a,y))-w*psi(a,y)
def critical(a,s):
    lo=mp.mpf('1e-20');hi=(2 if s=='+' else 1)-lo
    for _ in range(190):
        x=(lo+hi)/2
        if crit_equation(a,x,s)>0:lo=x
        else:hi=x
    x=(lo+hi)/2
    z=2*x/(2-x) if s=='+' else x/(1-x)
    return z,psi(a,1+x if s=='+' else 1-x)/(a*z)
def data(a,m,z,s):
    r=mp.mpf(2)/(m-1+z);q=1+r
    h=(2+r)*z/(z+2) if s=='+' else -(2+r)*z/(2*(1+z))
    if a==1:
        Q=q*mp.log(q)
        H=(q+h)*mp.log(q+h)-Q if s=='+' else (1+h)*mp.log1p(h)
        g=r*H/Q-h
    else:
        Q=mp.expm1(a*mp.log(q))
        H=(q+h)**a-q**a if s=='+' else mp.expm1(a*mp.log1p(h))
        g=(r*H-Q*h)/(Q-r)
    return r,Q,h,H,g
def body(a,r):
    if a==1:
        v=(1+r)*mp.log1p(r)/r
        return v-1-mp.log(v)
    Q=mp.expm1(a*mp.log1p(r));v=a*(Q-r)/((a-1)*Q)
    return mp.log(Q/(a*r))/(a-1)-mp.log(v)
def nu(a,m,z,s):
    r,Q,h,H,g=data(a,m,z,s)
    return g/(-m*mp.expm1(body(a,r)-body(a,mp.mpf(2)/(m-1))))
def linear(a,z,s):
    h=2*z/(z+2) if s=='+' else -z/(1+z)
    P=psi(a,1+h)
    J=((1 if s=='+' else 0)+h/2)*py(a,1+h)-a*(h+P)/2
    return 2*J/(a*z)+3*P/(2*a)
def kstar(a,D,r,Q,h,H):
    if a==1:return ((Q-r)*(D+h)-r*H)/(r*r)
    return (Q*(D+h)-a*r*(D+H))/((a-1)*r*Q)
def score(a,D,r,Q,h,H,k):
    Z=D+r*k+h
    if a==1:return (Q*k+H)/Z-mp.log(Z/D)
    return (mp.log((D+Q*k+H)/D)-a*mp.log(Z/D))/(a-1)
def rounded(a,m,n,z,s):
    D=m*n;r,Q,h,H,g=data(a,m,z,s)
    k=kstar(a,D,r,Q,h,H);ks=[int(mp.floor(k)),int(mp.ceil(k))]
    need(m*(m-1)//2<=ks[0]<=ks[1]<=D-m*(m+1)//2,'Nonphysical rounded rank')
    return max(score(a,D,r,Q,h,H,k) for k in ks)
def bulk(a,m,n):
    D=m*n;r=mp.mpf(2)/(m-1);q=1+r
    Q=q*mp.log(q) if a==1 else mp.expm1(a*mp.log(q))
    k=kstar(a,D,r,Q,0,0)
    return max(score(a,D,r,Q,0,0,int(mp.floor(k))),
               score(a,D,r,Q,0,0,int(mp.ceil(k))))

save()
try:
    p,b,ax=mp.findroot(lambda p,b,a:(crit_equation(a,p,'+'),crit_equation(a,b,'-'),
              psi(a,1+p)*(2-p)/(2*a*p)-psi(a,1-b)*(1-b)/(a*b)),
              (mp.mpf('.85'),mp.mpf('.61'),mp.mpf('.55')),tol=mp.mpf('1e-78'))
    zs={'+':2*p/(2-p),'-':b/(1-b)}
    d0=psi(ax,1+p)/(ax*zs['+'])
    As={s:linear(ax,z,s) for s,z in zs.items()}
    slopes={s:mp.diff(lambda a:psi(a,1+(2*z/(z+2) if s=='+' else -z/(1+z)))/(a*z),ax)
            for s,z in zs.items()}
    need(slopes['+']>0>slopes['-'],'Critical slope signs')
    uc=(As['-']-As['+'])/(slopes['+']-slopes['-']);ac=As['+']+slopes['+']*uc
    envelopes=[]
    for m in (80,160,320,640,1280):
        def eq(zp,zm,a):
            return (mp.diff(lambda z:nu(a,m,z,'+'),zp)/m**2,
                    mp.diff(lambda z:nu(a,m,z,'-'),zm)/m**2,
                    (nu(a,m,zp,'+')-nu(a,m,zm,'-'))/m**2)
        zp,zm,a=mp.findroot(eq,(zs['+'],zs['-'],ax+uc/m),tol=mp.mpf('1e-68'))
        need(max(abs(v) for v in eq(zp,zm,a))<mp.mpf('1e-60'),'Stationary crossing residual')
        center=nu(a,m,zp,'+')
        order_res=m*m*(a-ax-uc/m);value_res=center-d0*m*m-ac*m
        need(abs(order_res)<1000 and abs(value_res)<1000,'Finite envelope asymptotic control')
        test_n=int(mp.floor(center))-1
        for s,z in [('+',zp),('-',zm)]:
            need(rounded(a,m,test_n,z,s)>bulk(a,m,test_n),
                 'Actual integer-rank family failed below the continuous center')
        # Two one-unit envelope level points check the m^-2 order scale.
        level=[]
        for s,z,direction in [('-',zm,-1),('+',zp,1)]:
            zz,aa=mp.findroot(lambda zz,aa:(mp.diff(lambda t:nu(aa,m,t,s),zz)/m**2,
                         nu(aa,m,zz,s)-center-1),
                         (z,a+direction/(abs(slopes[s])*m*m)),tol=mp.mpf('1e-62'))
            need(direction*(aa-a)>0,'Wrong side of unit-level point')
            width=m*m*abs(aa-a)
            need(mp.mpf('.1')<width<100,'Unit-level order scale')
            level.append({'sign':s,'m2_order_width':st(width)})
        # The continuous envelope at the unshifted critical order is worse.
        base_z={s:mp.findroot(lambda z:mp.diff(lambda t:nu(ax,m,t,s),z),zs[s]) for s in ('+','-')}
        unshifted=max(nu(ax,m,base_z[s],s) for s in ('+','-'))
        need(unshifted>center,'Ignoring the 1/m order shift did not worsen the envelope')
        envelopes.append({'m':m,'order':st(a),'m2_order_remainder':st(order_res),
             'center_minus_quadratic_linear':st(value_res),'unshifted_loss_over_m':st((unshifted-center)/m),
             'unit_level_points':level})
    parameters=[]
    for a in map(mp.mpf,('.15','.4','.55','.75','1','1.5','4')):
        crits={s:critical(a,s) for s in ('+','-')}
        s=max(crits,key=lambda s:crits[s][1]);z,d=crits[s]
        parameters.append((a,s,z,d,linear(a,z,s)))
    B0=5+max(abs(x[4]) for x in parameters)
    barriers=[]
    for a,s,z,d,A in parameters:
        for m in (200,600,1800):
            n=int(mp.floor(d*m*m-B0*m));need(n>=m,'Barrier dimensions not physical')
            excess=rounded(a,m,n,z,s)-bulk(a,m,n)
            need(excess>0,'Actual lower barrier witness failed')
            barriers.append({'alpha':st(a),'m':m,'n':n,'sign':s,
                             'm4_actual_entropy_gain':st(m**4*excess)})
    out['groups']={'constants':{'alpha0':st(ax),'d0':st(d0),'uc':st(uc),'ac':st(ac),
                               'numerical_illustrations_only':True},
      'continuous_envelope':{'cases':len(envelopes),'samples':envelopes,
          'scope':'local stationary crossings and unit-level points, not a global numerical M_I certificate'},
      'actual_barrier':{'cases':len(barriers),'includes_von_Neumann':True,'finite_B0':st(B0),'samples':barriers},
      'rejected_mutation':'Setting the best order equal to alpha0 omits a positive O(m) continuous-onset penalty.'}
    out['status']='PASS'
except BaseException as exc:
    out.update(status='FAIL',error=str(exc),traceback=traceback.format_exc())
    print(out['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':out['status'],'run':str(run),'full_feasible_set_enumeration':False}),flush=True)
if out['status']!='PASS':sys.exit(1)
