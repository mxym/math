from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=70
def pieces(t):
    A=mp.expm1(t)
    q=t/A
    d=1-q
    w=-mp.log(q)
    s=mp.exp(t)/A-1/t
    sp=1/t**2-mp.exp(t)/A**2
    g=w-d
    gp=s*d
    gpp=sp*d+s*s*q
    e=t*s*q/d
    return g,gp,gpp,w,e
out={'scope':'finite floating-point discovery only; no inequalities certified','bounds':[]}
for which in ['curvature','elasticity_when_above_half']:
    minimum=None
    count=0
    negative=0
    for j in range(1,10001):
        t=mp.mpf(j)/1000
        g,gp,gpp,w,e=pieces(t)
        if which=='curvature':value=t*gpp/gp+g/2-1
        elif e>mp.mpf('0.5'):value=1-w/4-e
        else:continue
        count+=1
        if value<0:negative+=1
        if minimum is None or value<minimum[0]:minimum=(value,t)
    out['bounds'].append({'name':which,'points':count,'negative':negative,
                          'minimum':[mp.nstr(x,65) for x in minimum]})
dest=Path(__file__).with_name('MONOTONIC_SUFFICIENT_BOUNDS_DISCOVERY.json')
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
