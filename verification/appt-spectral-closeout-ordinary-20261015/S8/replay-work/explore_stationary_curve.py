from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=75
def pieces(k):
    q=k/mp.expm1(k);d=1-q;s=1-d/k
    sp=1/k**2-mp.exp(k)/mp.expm1(k)**2
    gp=s*d;gpp=sp*d+s*s*q
    return q,d,s,sp,gp,gpp
def J(K,x):
    k=K*x
    q,d,s,sp,gp,gpp=pieces(k)
    y=s+mp.mpf(2)/3*((1-x)**-2-1)
    yp=sp+mp.mpf(4)/(3*K*(1-x)**3)
    return K*(gpp/gp+y-yp/y)
out={'scope':'Floating discovery only, no global root count proof','rows':[]}
for ks in ['0.001','0.01','0.05','0.1','0.2','0.3','0.4','0.52']:
    K=mp.mpf(ks)
    roots=[]
    mesh=[mp.mpf(j)/1000 for j in range(1,1000)]
    mesh += [1-K*mp.mpf(j)/1000 for j in range(1,1000) if 0<1-K*mp.mpf(j)/1000<1]
    mesh=sorted(set(mesh))
    for l,r in zip(mesh,mesh[1:]):
        if J(K,l)*J(K,r)<0:
            root=mp.findroot(lambda x:J(K,x),(l,r),solver='anderson')
            if all(abs(root-v)>mp.mpf('1e-50') for v in roots):roots.append(root)
    out['rows'].append({'K':ks,'roots':[{'x':mp.nstr(x,65),'one_minus_x_over_K':mp.nstr((1-x)/K,65)} for x in roots]})
p=Path(__file__).with_name('STATIONARY_CURVE_DISCOVERY.json')
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,indent=2))
