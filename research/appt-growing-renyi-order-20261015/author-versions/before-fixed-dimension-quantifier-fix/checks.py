#!/usr/bin/env python3
"""Actual-state finite diagnostics, not a whole-feasible-set numerical proof."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys,traceback
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');run.mkdir(parents=True)
for n in ['PAPER.md','THEOREM_MAP.md','checks.py']:(run/n).write_bytes((here/n).read_bytes())
out={'status':'RUNNING','author_only':True,'new_Lean':False,
     'full_feasible_set_enumeration':False,'source_sha256':{
        n:hashlib.sha256((run/n).read_bytes()).hexdigest() for n in ['PAPER.md','THEOREM_MAP.md','checks.py']},'groups':{}}
def save():(run/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(t,msg):
    if not t:raise AssertionError(msg)
def st(x):return mp.nstr(x,30)
mp.dps=180
def logadd(u,v):
    high=max(u,v);return high+mp.log1p(mp.exp(min(u,v)-high))
def projection(m,D,alpha,k):
    theta=mp.mpf(k)/D;t=mp.mpf(2)/(m-1)
    return (logadd(mp.log1p(-theta),mp.log(theta)+alpha*mp.log1p(t))
              -alpha*mp.log1p(t*theta))/(alpha-1)
def spike(D,alpha):
    theta=mp.mpf(1)/D
    return (logadd(mp.log1p(-theta),mp.log(theta)+alpha*mp.log(3))
               -alpha*mp.log1p(2*theta))/(alpha-1)
def bounds(m,D,alpha):
    a=alpha-1;q=mp.mpf(m+1)/(m-1)
    T=max(mp.log(q),mp.log(3)-mp.log(D)/a)
    L=mp.log(2*alpha)/a+4/alpha+mp.mpf(4)/D
    U=mp.mpf(2)*m/(D-m)+2*mp.exp(-mp.sqrt(a))+2/mp.sqrt(a)+mp.log(48)/a
    return T,L,U

save()
try:
    pairs=[(2,2),(2,3),(2,100),(2,10**100),(3,3),(3,1000),(3,10**80),
           (10,10),(10,10**20),(100,100),(1000,1000),(10**6,10**6),(10**6,10**50)]
    rows=[];beyond=0
    for m,n in pairs:
        D=m*n
        orders=[mp.mpf(2),mp.mpf(3),mp.mpf(5),max(mp.mpf(2),mp.sqrt(mp.log(D))),
                max(mp.mpf(2),mp.log(D)/mp.log(3)),max(mp.mpf(2),2*mp.log(D)/mp.log(3)),
                mp.mpf(D),mp.mpf(10)*D]
        for alpha in orders:
            k=max(1,int(mp.floor(mp.mpf(D)/alpha)))
            need(1<=k<D and mp.mpf(k)/D>=1/(2*alpha),'Actual integer projection rank bounds')
            need(mp.mpf(k)/D<=1/alpha+mp.mpf(1)/D,'Actual projection upper fraction')
            star=spike(D,alpha);bulk=projection(m,D,alpha,k)
            singular=-mp.log1p(-mp.mpf(1)/D)
            T,L,U=bounds(m,D,alpha)
            need(max(star,bulk)>=T-L-mp.mpf('1e-140'),'Explicit finite lower bound failed')
            need(max(star,bulk,singular)<=T+U+mp.mpf('1e-140'),'Actual state above finite upper bound')
            need(min(star,bulk,singular)>=-mp.mpf('1e-140'),'Negative deficit for an actual state')
            if alpha>D:beyond+=1;need(k==1,'Large-order rank incorrectly fractional')
            rows.append({'m':m,'n':str(n),'alpha':st(alpha),'k':str(k),'T':st(T),
                         'actual_family_lower':st(max(star,bulk)),'lower_error':st(L),'upper_error':st(U)})
    # Exact trace normalization at an actual singular APPT state.
    normal=[]
    for D in (4,9,100,10**30):
        alpha=mp.mpf(7);raw=mp.log1p(-mp.mpf(1)/D)/(alpha-1)
        mean=1-mp.mpf(1)/D
        corrected=raw-alpha*mp.log(mean)/(alpha-1)
        exact=-mp.log1p(-mp.mpf(1)/D)
        need(abs(corrected-exact)<mp.mpf('1e-140'),'Raw-mean normalization identity')
        need(raw<0<exact,'Omitting normalization was not rejected')
        normal.append({'D':str(D),'wrong_raw_score':st(raw),'actual_deficit':st(exact)})
    D=2*10**100;alpha=mp.sqrt(mp.log(D));k=max(1,int(mp.floor(mp.mpf(D)/alpha)))
    fixed=projection(2,D,alpha,k)
    fake=max(mp.mpf(0),mp.log(3)-mp.log(D)/(alpha-1))
    need(fixed>mp.mpf('.5') and fake==0,'Dropping fixed-m bulk term not exposed')
    need(projection(2,200000,mp.mpf(2),100000)>mp.mpf('.2'),
         'False fixed-m bounded-order c=0 extension not exposed')
    out['groups']={'finite_actual_states':{'cases':len(rows),'alpha_greater_D_cases':beyond,'samples':rows},
        'trace_normalization':{'cases':len(normal),'samples':normal},
        'fixed_m_control':{'actual_projection_deficit':st(fixed),'false_joint_m_only_formula':st(fake)},
        'rejected_variants':['omit exact mean normalization','drop fixed-m bulk log(q)',
                             'use fractional rank D/alpha when alpha>D','claim c=0 zero for bounded order and fixed m'],
        'scope':'Finite actual-state controls support explicit analytic inequalities; no global numerical maximum certificate.'}
    out['status']='PASS'
except BaseException as exc:
    out.update(status='FAIL',error=str(exc),traceback=traceback.format_exc());print(out['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':out['status'],'run':str(run),'full_feasible_set_enumeration':False}),flush=True)
if out['status']!='PASS':sys.exit(1)
