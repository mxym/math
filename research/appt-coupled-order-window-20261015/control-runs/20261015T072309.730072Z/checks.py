#!/usr/bin/env python3
"""Finite coupled-window controls, not a full feasible-set proof."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,traceback,sys
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');run.mkdir(parents=True)
for n in ['PAPER.md','THEOREM_MAP.md','checks.py']:(run/n).write_bytes((here/n).read_bytes())
out={'status':'RUNNING','author_only':True,'new_Lean':False,'full_feasible_set_enumeration':False,
     'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in run.iterdir()},'groups':{}}
def save():(run/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(t,msg):
    if not t:raise AssertionError(msg)
def text(x):return mp.nstr(x,27)
mp.dps=90
def psi(alpha,y):return (mp.expm1(alpha*mp.log(y))-alpha*(y-1))/(alpha-1)
def dpsi(alpha,y):return alpha*mp.expm1((alpha-1)*mp.log(y))/(alpha-1)
def critical(alpha,sign):
    w=mp.mpf(2) if sign=='+' else mp.mpf(1)
    lo=mp.mpf('1e-15');hi=w-mp.mpf('1e-15')
    for _ in range(170):
        x=(lo+hi)/2;y=1+x if sign=='+' else 1-x
        F=x*(w-x)*(dpsi(alpha,y) if sign=='+' else -dpsi(alpha,y))-w*psi(alpha,y)
        if F>0:lo=x
        else:hi=x
    x=(lo+hi)/2
    z=2*x/(2-x) if sign=='+' else x/(1-x)
    return z,psi(alpha,1+x if sign=='+' else 1-x)/(alpha*z)
lo=mp.mpf('.5');hi=mp.mpf(1)
for _ in range(130):
    mid=(lo+hi)/2
    if critical(mid,'+')[1]>critical(mid,'-')[1]:hi=mid
    else:lo=mid
ax=(lo+hi)/2;zp,d0=critical(ax,'+');zm,_=critical(ax,'-')
zs={'+':zp,'-':zm}
def coefficient(alpha,z,sign):
    h=2*z/(z+2) if sign=='+' else -z/(1+z)
    P=psi(alpha,1+h);J=((1 if sign=='+' else 0)+h/2)*dpsi(alpha,1+h)-alpha*(h+P)/2
    return 2*J/(alpha*z)+3*P/(2*alpha)
As={s:coefficient(ax,z,s) for s,z in zs.items()}
slopes={s:mp.diff(lambda alpha:psi(alpha,1+(2*z/(z+2) if s=='+' else -z/(1+z)))/(alpha*z),ax)
        for s,z in zs.items()}
uc=(As['-']-As['+'])/(slopes['+']-slopes['-']);ac=As['+']+slopes['+']*uc
I=(min(zp,zm)/2,2*max(zp,zm))
def body(alpha,r):
    Q=mp.expm1(alpha*mp.log1p(r));s=alpha*(Q-r)/((alpha-1)*Q)
    return mp.log(Q/(alpha*r))/(alpha-1)-mp.log(s)
def terms(alpha,m,z,sign):
    r=mp.mpf(2)/(m-1+z);q=1+r;h=(2+r)*z/(z+2) if sign=='+' else -(2+r)*z/(2*(1+z))
    Q=mp.expm1(alpha*mp.log(q));H=(q+h)**alpha-q**alpha if sign=='+' else mp.expm1(alpha*mp.log1p(h))
    g=(r*H-Q*h)/(Q-r)
    return r,Q,h,H,g
def score(alpha,D,r,Q,h,H,k):
    return (mp.log((D+Q*k+H)/D)-alpha*mp.log((D+r*k+h)/D))/(alpha-1)
def golden(f,a,b):
    t=(mp.sqrt(5)-1)/2;x=b-t*(b-a);y=a+t*(b-a);fx=f(x);fy=f(y)
    for _ in range(220):
        if fx<fy:a=x;x=y;fx=fy;y=a+t*(b-a);fy=f(y)
        else:b=y;y=x;fy=fx;x=b-t*(b-a);fx=f(x)
    z=(a+b)/2
    return z,f(z)
def candidate_max(f):
    xs=[I[0]+(I[1]-I[0])*j/24 for j in range(25)]
    vals=[f(z) for z in xs];c=[(xs[0],vals[0]),(xs[-1],vals[-1])]
    for j in range(1,24):
        if vals[j]>=vals[j-1] and vals[j]>=vals[j+1]:c.append(golden(f,xs[j-1],xs[j+1]))
    return max(c,key=lambda x:x[1])
def bulk(alpha,m,D):
    r=mp.mpf(2)/(m-1);Q=mp.expm1(alpha*mp.log1p(r));k=D*(Q-alpha*r)/((alpha-1)*r*Q)
    return max(score(alpha,D,r,Q,0,0,int(mp.floor(k))),score(alpha,D,r,Q,0,0,int(mp.ceil(k))))

save()
try:
    need(slopes['+']>0 and slopes['-']<0,'transition slope signs')
    rows=[];max_scaled=mp.mpf(0);max_rank_error=mp.mpf(0);max_zrate=mp.mpf(0)
    scenarios=[(u,a) for u in map(mp.mpf,('-3','0','3')) for a in map(mp.mpf,('-2','0','1','3'))]
    scenarios += [(uc-1,ac),(uc,ac),(uc+1,ac)]
    strongest_mutation=mp.mpf(0);gapcases=0
    for u,atarget in scenarios:
        points=[]
        for m in (100,500,2000):
            n=int(mp.nint(d0*m*m+atarget*m));D=m*n;alpha=ax+u/m;a=(mp.mpf(n)-d0*m*m)/m
            G=bulk(alpha,m,D);pred=[mp.mpf(0)]+[ax*zs[s]*(As[s]+slopes[s]*u-a) for s in ('+','-')]
            predicted=max(pred);values={};zcases={};integer_values={}
            for sign in ('+','-'):
                def real(z):
                    r,Q,h,H,g=terms(alpha,m,z,sign)
                    return m*D*(body(alpha,r)-mp.log1p(-g/D)-G)
                z,value=candidate_max(real);values[sign]=value;zcases[sign]=z
                r,Q,h,H,g=terms(alpha,m,z,sign)
                k=(Q*(D+h)-alpha*r*(D+H))/((alpha-1)*r*Q)
                k0=int(mp.floor(k));k1=int(mp.ceil(k));R=m*(m-1)//2;K=m*(m+1)//2
                need(R<=k0<=k1<=D-K,'coupled actual rank outside physical range')
                integer_values[sign]=max(m*D*(score(alpha,D,r,Q,h,H,k0)-G),
                                         m*D*(score(alpha,D,r,Q,h,H,k1)-G))
                rankerr=abs(value-integer_values[sign])*m**4
                max_rank_error=max(max_rank_error,rankerr)
                need(rankerr<mp.mpf('1e5'),'integer rounding not O(m^-4) in scaled score')
                max_zrate=max(max_zrate,m*abs(z-zs[sign]))
            upper=max(mp.mpf(0),*values.values());lower=max(mp.mpf(0),*integer_values.values())
            need(lower<=upper+mp.mpf('1e-60'),'actual family lower above continuous envelope')
            scaled=abs(upper-predicted)*m;max_scaled=max(max_scaled,scaled)
            need(scaled<mp.mpf('1e4'),'coupled value error not consistent with O(1/m)')
            actual_label=max([('bulk',mp.mpf(0)),*values.items()],key=lambda x:x[1])[0]
            labels=['bulk','+','-'];order=sorted(range(3),key=lambda i:pred[i],reverse=True)
            gap=pred[order[0]]-pred[order[1]]
            if m==2000 and gap>mp.mpf('.1'):
                need(actual_label==labels[order[0]],'fixed gap sign selection failed');gapcases+=1
            no_drift=max([mp.mpf(0)]+[ax*zs[s]*(As[s]-a) for s in ('+','-')])
            if m==2000:strongest_mutation=max(strongest_mutation,abs(upper-no_drift))
            points.append({'m':m,'n':n,'u':text(u),'actual_a':text(a),'predicted':text(predicted),
                           'continuous_candidate_upper':text(upper),'physical_integer_lower':text(lower),
                           'm_absolute_error':text(scaled),'selected_candidate':actual_label})
        rows.append(points)
    need(strongest_mutation>mp.mpf('.1'),'omitting order drift mutation did not separate')
    onset=[]
    for u in (mp.mpf(-3),mp.mpf(0),mp.mpf(3),uc):
        for m in (100,500,2000):
            alpha=ax+u/m
            def nu(z,s):
                r,Q,h,H,g=terms(alpha,m,z,s)
                return g/(-m*mp.expm1(body(alpha,r)-body(alpha,mp.mpf(2)/(m-1))))
            candidates=[candidate_max(lambda z,s=s:nu(z,s)) for s in ('+','-')]
            center=max(v for z,v in candidates);linear=max(As[s]+slopes[s]*u for s in ('+','-'))
            residual=center-d0*m*m-linear*m
            need(abs(residual)<mp.mpf('1e4'),'uniform onset bounded remainder inconsistent')
            onset.append({'u':text(u),'m':m,'after_quadratic_linear':text(residual)})
    out['groups']={'transition_constants':{'alpha0':text(ax),'d0':text(d0),'z':{s:text(z) for s,z in zs.items()},
          'A':{s:text(x) for s,x in As.items()},'slopes':{s:text(x) for s,x in slopes.items()},
          'frontier_u_crossing':text(uc),'frontier_a_crossing':text(ac),
          'precision_note':'numerical illustrations, not exact definitions or rigorous intervals'},
      'value_and_ranks':{'actual_dimension_cases':len(scenarios)*3,'fixed_gap_cases':gapcases,
          'maximum_m_score_error':text(max_scaled),'maximum_m4_integer_loss':text(max_rank_error),
          'maximum_m_z_displacement':text(max_zrate),'samples':rows,
          'rejected_mutations':['omit order drift in coupled law']},
      'onset':{'cases':len(onset),'samples':onset}}
    out['status']='PASS'
except BaseException as exc:
    out['status']='FAIL';out['error']=str(exc);out['traceback']=traceback.format_exc();print(out['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':out['status'],'run':str(run),
      'scope':'finite compact multistart scalar candidates and physical-rank lower/real upper; whole feasible set proved analytically'}),flush=True)
if out['status']!='PASS':sys.exit(1)
