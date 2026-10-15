"""Finite exact loss diagnostics on actual APPT constructions, not a full audit."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as Q
import hashlib,json,shutil,traceback
import mpmath as mp
mp.mp.dps=120
base=Path(__file__).resolve().parent
out=base/'control-runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out.mkdir(parents=True,exist_ok=False)
for name in ['PAPER.md','THEOREM_MAP.md','checks.py']:
    shutil.copyfile(base/name,out/name)
inputs={n:hashlib.sha256((out/n).read_bytes()).hexdigest() for n in ['PAPER.md','THEOREM_MAP.md','checks.py']}
(out/'INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n')

def ass(cond,label):
    if not cond:raise AssertionError(label)

def data(m,ys,alpha):
    D=len(ys);ys=sorted(ys,reverse=True)
    R=m*(m-1)//2;K=m*(m+1)//2;j=D-K+1
    middle=ys[R-1:j];N=D-m*m+2
    ass(len(middle)==N,'middle cardinality')
    A=middle[-1];B=middle[0];mu=sum(middle,Q(0))/N
    kappa=B/A-1;L=(m-1)*kappa
    theta=(mu/A-1)/kappa if kappa else Q(0)
    eta=2*(m-2)*kappa*kappa/(2-(m-3)*kappa)
    C=Q(0);J=Q(0)
    for y in middle:
        z=(m-1)*(y/A-1);u=z/L if L else Q(0)
        J+=z*(L-z)/N
        C+=A**alpha*(1+u*((1+kappa)**alpha-1)-(1+kappa*u)**alpha)/D
    P=(A**alpha*(3-eta)**alpha-ys[0]**alpha)/D
    T=sum((y**alpha for i,y in enumerate(ys) if i!=0 and not R-1<=i<j),Q(0))/D
    M=sum((y**alpha for y in ys),Q(0))/D
    leading=Q(N,D)*A**alpha*(1+theta*((1+kappa)**alpha-1))+A**alpha*(3-eta)**alpha/D
    ass(0<=kappa<=Q(2,m-1) and 0<=theta<=1,'actual parameter interval')
    ass(C>=0 and J>=0 and P>=0,'nonnegative exact physical losses')
    ass(M==leading-C-P+T,'exact loss identity')
    ass((C==0)==(J==0),'strict chord equality versus endpoint spread')
    return {'C':C,'J':J,'P':P,'M':M,'leading':leading,'T':T,'theta':theta,'L':L}

def normalize(raw):
    D=len(raw);s=sum(raw,Q(0))/D
    return [x/s for x in raw]

try:
    cases=0;lossyC=None;lossyP=None
    for m,n in [(3,3),(3,7),(4,4),(4,10),(5,5),(5,12)]:
        D=m*n;t=Q(2,m-1)
        spectra=[]
        # Every contraction X with 0<=X<=I gives all-unitary APPT I+tX.
        for pattern in [[Q(0),Q(1,2),Q(1)], [Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)]]:
            spectra.append(normalize([1+t*pattern[i%len(pattern)] for i in range(D)]))
        for k in [1,max(1,D//3),D-1]:
            for width in [Q(0),t/3,t]:
                eta=2*(m-2)*width*width/(2-(m-3)*width)
                d=2-width-eta
                raw=[Q(3)-eta]+[1+width]*(k-1)+[Q(1)]*(D-k)
                ass(sum(raw)==D+width*k+d,'actual full trace')
                spectra.append(normalize(raw))
        # Convex combinations of permuted physical orbit points remain APPT.
        first=normalize([Q(3)]+[Q(1)]*(D-1))
        second=normalize([1+t]*(D//2)+[Q(1)]*(D-D//2))
        third=list(reversed(first))
        spectra.append([(first[i]+2*second[i]+third[i])/4 for i in range(D)])
        for ys in spectra:
            ass(sum(ys)==D,'actual trace-one normalization')
            for alpha in [2,3,5,8,12]:
                v=data(m,ys,alpha);cases+=1
                if v['C']>0:lossyC=v
                if v['P']>0:lossyP=v
    ass(lossyC is not None and lossyP is not None,'nonzero losses are actually exercised')
    rejects=[]
    for name,condition,why in [
        ('omit-middle-chord-loss',lossyC['M']==lossyC['leading']-lossyC['P']+lossyC['T'],
         'an actual multi-level contraction has positive middle spread'),
        ('omit-actual-peak-loss',lossyP['M']==lossyP['leading']-lossyP['C']+lossyP['T'],
         'the actual head can lie strictly below its permitted cap'),
        ('omit-middle-cardinality-shift',9-3*3==9-3*3+2,
         'the inclusive middle range has D-m^2+2 slots, not D-m^2'),
        ('replace-centered-body-law-by-raw-endpoints',Q(2,3)==0,
         'uncentered endpoints 0,2 with upper weight 1/3 have nonzero mean; trace centering is essential')]:
        ass(not condition,'false loss variant survived '+name)
        record={'status':'REJECTED','name':name,'reason':why}
        rejects.append(record);(out/('REJECTED-'+name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    rows=[]
    for m in [10,20,50,100,300]:
        alpha=m
        D=m*((3**alpha+m-1)//m)
        l=mp.mpf(1);h=mp.mpf('.3');k=int(mp.floor(h*D))
        width=l/(m-1);eta=2*(m-2)*width**2/(2-(m-3)*width);d=2-width-eta
        scale=1+width*mp.mpf(k)/D+d/D
        top=(3-eta)/scale
        rows.append({'m':m,'scaled_peak_correction':str(m*(3-top)),
                     'interior_limit':str(3*l*h+2*l*l/(2-l))})
    bulk=[]
    c=mp.mpf(1);h=mp.mpf('.5')-1/mp.expm1(2)
    for m in [20,50,100,300]:
        alpha=m;D=m*((9**alpha+m-1)//m);k=int(mp.floor(h*D))
        theta=mp.mpf(k)/D
        for name,L in [('projection-only',mp.mpf(2)),('protected-spike',2-1/mp.sqrt(m))]:
            width=L/(m-1);eta=2*(m-2)*width**2/(2-(m-3)*width);d=2-width-eta
            scale=1+width*theta+d/D
            top=(3-eta)/scale
            moment=((3-eta)**alpha+(k-1)*(1+width)**alpha+(D-k))/D/scale**alpha
            bulk.append({'m':m,'family':name,'top':str(top),'log_moment':str(mp.log(moment)),
                         'bulk_limit':str(mp.log(mp.expm1(2)/2)-1+2/mp.expm1(2)),
                         'actual_projection_rank_integer':True})
    (out/'MOVING_WINDOW_CONTROLS.json').write_text(json.dumps({'interior':rows,'bulk_two_families':bulk},indent=2)+'\n')
    result={'status':'PASS','input_sha256':inputs,'exact_physical_loss_cases':cases,
        'moving_window_geometry_cases':len(rows)+len(bulk),'false_variants_rejected':len(rejects),
        'whole_APPT_quantifiers_or_asymptotic_limits_numerically_certified':False,
        'independent_review':False,'new_Lean':False}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'run':str(out),**result}))
except Exception:
    (out/'RESULT.json').write_text(json.dumps({'status':'FAIL','input_sha256':inputs,
         'traceback':traceback.format_exc()},indent=2)+'\n')
    raise
