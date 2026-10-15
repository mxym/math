#!/usr/bin/env python3
"""Finite diagnostics for M's tiny and unbounded-order escape exclusions."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,sys,traceback
from mpmath import mp

here=Path(__file__).resolve().parent
run=here/'global-control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
run.mkdir(parents=True)
names=['GLOBAL_ORDER.md','GLOBAL_TARGET.md','global_checks.py','checks.py','PAPER.md','THEOREM_MAP.md']
for n in names:(run/n).write_bytes((here/n).read_bytes())
out={'status':'RUNNING','author_only':True,'new_Lean':False,
     'finite_diagnostics_not_full_quantified_proof':True,
     'source_sha256':{n:hashlib.sha256((run/n).read_bytes()).hexdigest() for n in names},'groups':{}}
def save():(run/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
def need(t,msg):
    if not t:raise AssertionError(msg)
def st(x):return mp.nstr(x,30)
# Reuse only explicitly selected pure scalar functions, not L's execution,
# filesystem setup, source binding, solver or actual diagnostics.
selected={'psi','py','data','body','nu','kstar','score','rounded','bulk'}
parsed=ast.parse((here/'checks.py').read_text())
pure=ast.Module(body=[x for x in parsed.body if isinstance(x,ast.FunctionDef) and x.name in selected],type_ignores=[])
exec(compile(pure,str(here/'checks.py')+'[pure-functions-only]','exec'),globals())
mp.dps=1250
prior=here/'control-runs'/'20261015T080542.309850Z'/'RESULT.json'
constants=json.loads(prior.read_text())['groups']['constants']
ax=mp.mpf(constants['alpha0']);d0=mp.mpf(constants['d0']);ac=mp.mpf(constants['ac']);B=abs(ac)+2
save()
try:
    tiny=[];moderate=[];large=[];derivatives=[]
    for m in (2000,8000,32000):
        n=int(mp.floor(d0*m*m+B*m));D=m*n;delta=mp.mpf(D)/m**3
        zm=(1+mp.sqrt(5))/2
        for a in map(mp.mpf,('.5','.2','.01','1e-20','1e-100','1e-1000')):
            excess=rounded(a,m,n,zm,'-')-bulk(a,m,n)
            gain=D*excess/a
            need(gain>0,'Tiny-order actual negative witness failed')
            tiny.append({'m':m,'alpha':st(a),'D_gain_over_alpha':st(gain)})
        star=mp.mpf(5)/(2*mp.log(2))*mp.log(m)
        t=mp.mpf(2)/(m-1)
        for a in [mp.mpf(2),mp.mpf(3),mp.mpf(5),star/2,star]:
            Qt=mp.expm1(a*mp.log1p(t));kr=kstar(a,D,t,Qt,0,0)
            ks=[int(mp.floor(kr)),int(mp.ceil(kr))]
            k=max(ks,key=lambda k:score(a,D,t,Qt,0,0,k))
            need(m*(m-1)//2<=k<=D-m*(m+1)//2,'Bulk winning integer rank not physical')
            r,Q,h,H,g=data(a,m,mp.mpf(2),'+')
            head=score(a,D,r,Q,h,H,k);middle=score(a,D,r,Q,0,0,k)
            G=score(a,D,t,Qt,0,0,k)
            ratio=D*(head-middle)/psi(a,2);loss=D*(G-middle)/a
            need(head>G,'Moderate-growing-order witness failed')
            need(abs(ratio-1)<20*(a/m+1/mp.sqrt(m)),'Relative head gain bound inconsistent')
            need(loss<=2*delta*(1+20*a/m),'Relative body penalty bound inconsistent')
            moderate.append({'m':m,'alpha':st(a),'head_gain_over_kernel':st(ratio),
                             'body_loss_over_alpha':st(loss),'D_profit_over_alpha':st(D*(head-G)/a)})
            theta=mp.mpf(k)/D
            for rr in [r,(r+t)/2,t]:
                q=1+rr
                exact=a*theta*(1-theta)*mp.expm1((a-1)*mp.log(q))/(a-1)/((1+theta*mp.expm1(a*mp.log(q)))*(1+theta*rr))
                numerical=mp.diff(lambda v:score(a,D,v,mp.expm1(a*mp.log1p(v)),0,0,k),rr)
                need(abs(exact-numerical)<mp.mpf('1e-1150'),'Exact binary-body derivative identity failed')
                relative=exact/(a*theta*(1-theta)*rr)
                need(abs(relative-1)<8*a*rr,'Uniform growing-order body derivative control')
                derivatives.append(st(abs(relative-1)/(a*rr)))
        # Hold ONE actual state selected at star fixed for all later orders.
        Qt=mp.expm1(star*mp.log1p(t));kr=kstar(star,D,t,Qt,0,0)
        k=max([int(mp.floor(kr)),int(mp.ceil(kr))],key=lambda k:score(star,D,t,Qt,0,0,k))
        bound=mp.log1p(t);past=None
        for a in [star,2*star,mp.mpf(1000),mp.mpf('1e6'),mp.mpf('1e12')]:
            r,Q,h,H,g=data(a,m,mp.mpf(2),'+')
            value=score(a,D,r,Q,h,H,k)
            need(value>bound,'One fixed high-order state failed to beat ALL-order bulk upper bound')
            if past is not None:need(value>=past,'Entropy-order monotonicity failed for one fixed state')
            past=value
            large.append({'m':m,'alpha':st(a),'state_deficit':st(value),'bulk_infinity_upper':st(bound)})
    out['groups']={'constants_from_author_L_result':{'source':str(prior.relative_to(here)),
          'sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),'constants':constants},
        'tiny_orders':{'cases':len(tiny),'smallest_alpha':'1e-1000','precision_digits':mp.dps,'samples':tiny},
        'growing_orders':{'cases':len(moderate),'samples':moderate},
        'exact_derivative':{'cases':len(derivatives),'maximum_scaled_relative_error':max(derivatives,key=mp.mpf)},
        'unbounded_order_examples':{'cases':len(large),'largest_alpha':'1e12','same_state_for_each_m':True,'samples':large},
        'scope':'Finite diagnostics support, but do not replace, the uniform analytic M0-M2 proof.'}
    out['status']='PASS'
except BaseException as exc:
    out.update(status='FAIL',error=str(exc),traceback=traceback.format_exc());print(out['traceback'],flush=True)
finally:
    save();print(json.dumps({'status':out['status'],'run':str(run),'full_quantified_proof':False}),flush=True)
if out['status']!='PASS':sys.exit(1)
