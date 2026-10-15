"""Finite author diagnostics, not certification of the full APPT optimum."""
from pathlib import Path
from fractions import Fraction as Q
from datetime import datetime,timezone
import hashlib,json,shutil,traceback
import mpmath as mp

mp.mp.dps=110
base=Path(__file__).resolve().parent
tag=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out=base/'control-runs'/tag;out.mkdir(parents=True,exist_ok=False)
for name in ['PAPER.md','THEOREM_MAP.md','checks.py']:
    shutil.copyfile(base/name,out/name)
manifest={name:hashlib.sha256((out/name).read_bytes()).hexdigest()
          for name in ['PAPER.md','THEOREM_MAP.md','checks.py']}
(out/'INPUTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
stats={};rejects=[]

def ass(condition,label):
    if not condition:raise AssertionError(label)

def reject(name,false_condition,detail):
    ass(not false_condition,'false variant survived: '+name)
    value={'status':'REJECTED','name':name,'reason':detail}
    rejects.append(value)
    (out/('REJECTED-'+name+'.json')).write_text(json.dumps(value,indent=2)+'\n')

def logadd(x,y):
    z=max(x,y)
    return z+mp.log(mp.exp(x-z)+mp.exp(y-z))

def log_projection_moment(D,alpha,t,k):
    theta=mp.mpf(k)/D
    return logadd(mp.log1p(-theta),mp.log(theta)+alpha*mp.log1p(t))-alpha*mp.log1p(t*theta)

def log_pole_moment(D,alpha):
    return logadd(mp.log1p(-mp.mpf(1)/D),alpha*mp.log(3)-mp.log(D))-alpha*mp.log1p(mp.mpf(2)/D)

def log_scalar(c,r,L,theta):
    logbulk=logadd(mp.log1p(-theta) if theta<1 else mp.ninf,
                   mp.log(theta)+c*L if theta>0 else mp.ninf)-c*L*theta
    if r==0 or L==2:return logbulk
    g=2*c*L*L/(3*(2-L))
    return logadd(logbulk,mp.log(r)-g-c*L*theta)

try:
    count=0
    for alpha in range(2,29):
        for v in [Q(1),Q(5,4),Q(3,2),Q(7,4),Q(2)]:
            for z in [Q(0),Q(1,100),Q(1,10),Q(1,3),Q(2,3),Q(1)]:
                p=(3-v)*z
                remainder=(v+p)**alpha-v**alpha-alpha*v**(alpha-1)*p
                ass(0<=remainder<=3**alpha*p*p,'exact rational remainder')
                if p:
                    endpoint=(3**alpha-v**alpha-alpha*v**(alpha-1)*(3-v))/(3-v)**2
                    ass(remainder/(p*p)<=endpoint,'monotone divided remainder')
                count+=1
    stats['exact_rational_remainder_cases']=count
    count=0
    for alpha in map(mp.mpf,['2','2.001','2.5','3.75','11.25','100.5','1000.25']):
        for v in map(mp.mpf,['1','1.0001','1.5','1.9999','2']):
            endpoint=(mp.power(3,alpha)-v**alpha-alpha*v**(alpha-1)*(3-v))/(3-v)**2
            last=mp.mpf(0)
            for fraction in map(mp.mpf,['.00001','.001','.05','.3','.8','1']):
                p=(3-v)*fraction
                remainder=((v+p)**alpha-v**alpha-alpha*v**(alpha-1)*p)/(p*p)
                tol=mp.power(3,alpha)*mp.mpf('1e-85')
                ass(remainder>=last-tol and remainder<=endpoint+tol,'real-order divided remainder')
                last=remainder;count+=1
    stats['real_order_remainder_cases']=count
    count=0;lower_count=0
    for m in [3,4,8,19,64]:
        t=mp.mpf(2)/(m-1);q=1+t
        for n in [m,2*m,50*m,10**8]:
            D=m*n
            for alpha in map(mp.mpf,['2','2.125','7.5','35','300','100000']):
                a=alpha-1
                H=max(mp.log(q),mp.log(3)-mp.log(D)/a)
                upper=H+mp.log(27)/a+4*mp.mpf(m)/(D-m)
                pole=log_pole_moment(D,alpha)/a
                ass(pole<=upper+mp.mpf('1e-80'),'physical pole finite upper')
                for k in sorted(set([1,2,D//3,D//2,D-1])):
                    val=log_projection_moment(D,alpha,t,k)/a
                    ass(val<=upper+mp.mpf('1e-80'),'physical projection finite upper')
                    count+=1
                if alpha*t>=2 and D/(alpha*t)>=2:
                    k=int(mp.floor(D/(alpha*t)))
                    val=log_projection_moment(D,alpha,t,k)/a
                    lower=mp.log(q)-(mp.log(2*alpha*t)+1)/a
                    ass(val>=lower-mp.mpf('1e-80'),'integer-rank finite lower')
                    lower_count+=1
    stats['actual_projection_upper_comparisons']=count
    stats['actual_width_adapted_integer_rank_lower_comparisons']=lower_count
    count=0
    for c in map(mp.mpf,['1','1.5','3','10','50','300']):
        B=mp.expm1(2*c)
        bulk=mp.log(B/(2*c))-1+2*c/B
        ass(bulk>=2*c-mp.log(2*c)-2,'large-c bulk endpoint')
        for r in map(mp.mpf,['0','.001','1','1000','1e30','1e300']):
            W=max(2*c,mp.log1p(r))
            ass(max(bulk,mp.log1p(r))>=W-mp.log(2*c)-2,'scalar lower bracket')
            for L in map(mp.mpf,['0','.05','.5','1','1.95','2']):
                for theta in map(mp.mpf,['0','.001','.05','.5','.9','1']):
                    val=log_scalar(c,r,L,theta)
                    ass(val<=W+mp.log(2)+mp.mpf('1e-80'),'scalar universal upper bracket')
                    count+=1
    stats['scalar_profile_sample_bracket_checks']=count
    reject('omit-linear-taylor-term',Q(101,100)**2<=Q(1)+9*Q(1,100)**2,
           'alpha=2,v=1,p=1/100 needs its positive linear term')
    reject('alpha-free-remainder-without-three-power',3**10-1-20<=4,
           'v=1,p=2,alpha=10 has remainder larger than p^2')
    raw=mp.log((1+mp.power(2,20))/2)/19
    actual=log_projection_moment(30,mp.mpf(20),mp.mpf(1),15)/19
    reject('omit-trace-normalization',mp.almosteq(raw,actual),
           'actual (I+P)/(D+k) differs from its unnormalized raw spectrum')
    fixedm=3;t=mp.mpf(1);alpha=mp.mpf(2);D=3*10**8
    val=log_projection_moment(D,alpha,t,D//3)
    reject('finite-projection-entropy-equals-log-q',mp.almosteq(val,mp.log(2)),
           'the exact finite m=3,alpha=2 projection entropy is not logq; this is not a bound on the unknown full optimum')
    for m,c in [(20,3),(100,5),(400,8)]:
        alpha=mp.mpf(m)*c;t=mp.mpf(2)/(m-1)
        # An actual integer D=m*n above 3^alpha; both normalization and rank retained.
        D=m*int(mp.ceil(mp.power(3,alpha)/m))
        k=int(mp.floor(D/(alpha*t)))
        deficit=log_projection_moment(D,alpha,t,k)/(alpha-1)
        naive=mp.log1p(mp.power(3,alpha)/D+alpha*(alpha-1)/(2*m*m))/(alpha-1)
        ass(deficit>naive,'old independent peak-plus-quadratic extrapolation must fail')
    stats['superlinear_naive_quadratic_counterexamples']=3
    result={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'input_sha256':manifest,
        'counts':stats,'rejected_false_variants':rejects,'precision_decimal_digits':mp.mp.dps,
        'full_APPT_optimization_numerically_certified':False,
        'finite_cases_are_not_proofs_of_limits_or_universal_quantifiers':True,
        'independent_review':False,'new_Lean':False}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'run':str(out),'status':'PASS','counts':stats,'false_variants_rejected':len(rejects)}))
except Exception:
    (out/'RESULT.json').write_text(json.dumps({'status':'FAIL','counts_before_failure':stats,
        'input_sha256':manifest,'traceback':traceback.format_exc()},indent=2)+'\n')
    raise
