#!/usr/bin/env python3
"""Discovery only: rational candidate tangent points from floating optimization."""
from math import log,lgamma,sqrt
from scipy.optimize import minimize
from pathlib import Path
import json,time
A=.0435;B=.0055;T=.049;DEN=10**9
rows=[];worst=(-1e9,None);start=time.monotonic()
for r in range(1,200):
    for s in range(r,200):
        n=r+s
        lc=r*log(r)+s*log(s)-n*log(n)+lgamma(n+1)-lgamma(r+1)-lgamma(s+1)
        a4=1/(r+1)**3-r/(n*(n+1)**3)
        b4=1/(s+1)**3-s/(n*(n+1)**3)
        def fn(p):
            h,j=p;x=(r*j+s*h)/n;v=r*h+s*j
            g2=h*h/(r+1)+j*j/(s+1)-v*v/(n*n*(n+1))
            g4=a4*h**4+b4*j**4
            value=lc+log(x)-A*g2-B*g4+T
            gh=s/(n*x)-A*(2*h/(r+1)-2*r*v/(n*n*(n+1)))-4*B*a4*h**3
            gj=r/(n*x)-A*(2*j/(s+1)-2*s*v/(n*n*(n+1)))-4*B*b4*j**3
            return -value,[-gh,-gj]
        seed=[min(r+1,max(2,sqrt((r+1)/(3*A)))),min(s+1,max(2,sqrt((s+1)/(3*A))))]
        result=minimize(fn,seed,jac=True,bounds=[(2,r+1),(2,s+1)],method='L-BFGS-B',
                        options={'ftol':1e-15,'gtol':1e-12,'maxiter':200,'maxls':40})
        nums=[max(2*DEN,min((d+1)*DEN,round(v*DEN))) for d,v in zip([r,s],result.x)]
        pt=[v/DEN for v in nums];neg,ngrad=fn(pt);grads=[-v for v in ngrad]
        support=sum(g*((d+1 if g>0 else 2)-p) for g,d,p in zip(grads,[r,s],pt))
        bound=-neg+support
        if bound>worst[0]:worst=(bound,(r,s,pt,result.message))
        rows.append([r,s,*nums])
    if r%20==0:print(r,round(time.monotonic()-start,1),worst,flush=True)
(Path(__file__).resolve().parent / 'mixed_finite_points.json').write_text(json.dumps({
 'schema':1,'alpha':[87,2000],'beta':[11,2000],'T':[49,1000],
 'dimension_max':199,'denominator':DEN,'points':rows},separators=(',',':'))+'\n')
print('DONE',len(rows),round(time.monotonic()-start,1),worst,flush=True)
