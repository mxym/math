"""New reviewer code; no author import or execution. Finite diagnostics only."""
from pathlib import Path
from fractions import Fraction as Q
from datetime import datetime,timezone
import hashlib,json,shutil,traceback
import mpmath as mp
import sympy as sp

mp.mp.dps=160
base=Path(__file__).resolve().parent
out=base/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out.mkdir(parents=True,exist_ok=False)
shutil.copyfile(__file__,out/'independent_checks.py')
shutil.copyfile(base/'INPUT_MANIFEST.json',out/'INPUT_MANIFEST.json')
stats={};rejections=[]
def must(test,msg):
    if not test:raise AssertionError(msg)
def reject(name,incorrect_assertion,observations):
    try:must(incorrect_assertion,name)
    except AssertionError as e:
        row={'name':name,'status':'REJECTED','actual_exception':repr(e),'observations':observations}
        rejections.append(row);(out/('REJECTED-'+name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    else:raise AssertionError('incorrect assertion survived: '+name)
def real(q):
    return mp.mpf(q.numerator)/q.denominator if isinstance(q,Q) else mp.mpf(q)
def stable_sum_log(terms):
    values=[mp.log(real(n))+a*mp.log(real(x)) for x,n,a in terms if n and x>0]
    top=max(values);return top+mp.log(mp.fsum(mp.exp(v-top) for v in values))
def entropy_from_raw(groups,alpha):
    D=sum(n for x,n in groups);trace=sum(x*n for x,n in groups)
    return (stable_sum_log([(x,n,alpha) for x,n in groups])+(alpha-1)*mp.log(D)-alpha*mp.log(real(trace)))/(alpha-1)
def scalar_log(c,logr,L,theta):
    vals=[]
    if theta<1:vals.append(mp.log1p(-theta)-c*L*theta)
    if theta>0:vals.append(mp.log(theta)+c*L*(1-theta))
    if logr!=mp.ninf and L<2:vals.append(logr-2*c*L*L/(3*(2-L))-c*L*theta)
    top=max(vals);return top+mp.log(mp.fsum(mp.exp(x-top) for x in vals))
def spectral_inputs(groups,m):
    D=sum(n for x,n in groups);R=m*(m-1)//2;K=m*(m+1)//2
    def at(i):
        for x,n in groups:
            if i<=n:return x
            i-=n
        raise AssertionError('rank index outside dimension')
    b=at(D-K+1);must(b>0,'pivot positive')
    v=at(R)/b;count=R;psum=Q(0);psquare=Q(0)
    for x,n in groups:
        use=min(n,count);p=x/b-v
        if use:must(p>=0,'head positive');psum+=use*p;psquare+=use*p*p
        count-=use
        if count==0:break
    must(1<=v<=(m+1)/Q(m-1),'middle width')
    must(all(0<=x/b<=3 for x,n in groups),'all eigenvalue bounds')
    must(psum<=m and psquare<=8,'head budgets')
    rawmean=sum(x*n for x,n in groups)/(D*b)
    must(rawmean>=1-Q(m,D),'exact mean lower bound')
    return b,v,psum,psquare

try:
    # Global algebraic expressions, distinct from finite numerical sampling.
    K,z=sp.symbols('K z',real=True)
    bulk=sp.exp(-K*z)*(1+z*(sp.exp(K)-1))
    must(sp.simplify(sp.diff(bulk,K)-z*(1-z)*sp.exp(-K*z)*(sp.exp(K)-1))==0,'bulk width derivative')
    C=sp.symbols('C',positive=True)
    coupled=sp.exp(-K*z)*(C+z*(sp.exp(K)-1))
    must(sp.simplify(sp.diff(coupled,z)-sp.exp(-K*z)*(sp.exp(K)-1-K*C-K*z*(sp.exp(K)-1)))==0,'mixing derivative')
    stats['symbolic_identities']=2
    count=0
    for alpha in range(2,22):
        for v in [Q(1),Q(6,5),Q(3,2),Q(2)]:
            last=Q(0)
            for h in [Q(0),Q(1,1000),Q(1,20),Q(1,3),Q(3,4),Q(1)]:
                p=(3-v)*h
                rem=(v+p)**alpha-v**alpha-alpha*v**(alpha-1)*p
                must(0<=rem<=3**alpha*p*p,'rational Taylor bound')
                if p:
                    value=rem/(p*p)
                    endpoint=(3**alpha-v**alpha-alpha*v**(alpha-1)*(3-v))/(3-v)**2
                    must(last<=value<=endpoint,'divided remainder monotone');last=value
                count+=1
    stats['exact_rational_remainder_cases']=count
    count=0
    for alpha in map(mp.mpf,['2.001','2.5','3.75','22.5','100.125','500.125']):
        for v in map(mp.mpf,['1','1.2','1.5','2']):
            last=0
            for h in map(mp.mpf,['1e-6','.002','.04','.5','1']):
                p=(3-v)*h
                val=((v+p)**alpha-v**alpha-alpha*v**(alpha-1)*p)/(p*p)
                tol=mp.power(3,alpha)*mp.mpf('1e-120')
                must(last<=val+tol and val<=mp.power(3,alpha)+tol,'noninteger remainder');last=val;count+=1
    stats['real_order_remainder_cases']=count
    count=0;lowercount=0
    for m in [3,4,7,12,29]:
        for n in [m,m*m+1,10**7]:
            D=m*n;t=Q(2,m-1);q=1+t
            state_groups=[[(Q(1),D)],[(Q(3),1),(Q(1),D-1)],[(Q(13,5),1),(Q(7,5),1),(Q(1),D-2)],[(Q(1),D-1),(Q(0),1)]]
            for k in sorted(set([1,D//3,D//2,D-1])):state_groups.append([(q,k),(Q(1),D-k)])
            for groups in state_groups:
                b,v,psum,psquare=spectral_inputs(groups,m)
                # Check the key finite power estimate at integer orders by exact arithmetic.
                for alpha in [2,3,7,17]:
                    lhs=sum((x/b)**alpha*n0 for x,n0 in groups)/D
                    rhs=v**alpha+Q(alpha*m,D)*v**(alpha-1)+Q(8,D)*3**alpha
                    must(lhs<=rhs,'finite R11 on physical spectrum')
                for alpha in map(mp.mpf,['2','2.25','4.5','30','1000','1000000']):
                    H=max(mp.log(real(q)),mp.log(3)-mp.log(D)/(alpha-1))
                    upper=H+mp.log(27)/(alpha-1)+4*mp.mpf(m)/(D-m)
                    actual=entropy_from_raw(groups,alpha)
                    must(actual<=upper+mp.mpf('1e-120'),'finite original-domain state upper')
                    count+=1
            for alpha in map(mp.mpf,['2','3.5','6','25','120','500','100000']):
                width=alpha*real(t)
                if width<2 or mp.mpf(D)/width<2:continue
                k=int(mp.floor(mp.mpf(D)/width));must(1<=k<D,'integer rank')
                theta=mp.mpf(k)/D
                must(1/(2*width)<=theta<=1/width,'floor bounds')
                actual=entropy_from_raw([(q,k),(Q(1),D-k)],alpha)
                lower=mp.log(real(q))-(mp.log(2*width)+1)/(alpha-1)
                must(actual>=lower-mp.mpf('1e-120'),'finite width-adapted lower')
                lowercount+=1
    stats['actual_physical_spectrum_upper_cases']=count
    stats['applicable_integer_rank_lower_cases']=lowercount
    stats['actual_physical_types']=['maximally mixed','pole','two noncommuting pure-spike mixture','singular I-vv*','all-rank projection']
    count=0
    for c in map(mp.mpf,['1','1.25','2','7','50','500']):
        B=mp.expm1(2*c);logbulk=mp.log(B/(2*c))-1+2*c/B
        for logr in [mp.ninf,-1000,-1,0,3,100,10000]:
            peak=mp.log1p(mp.exp(logr)) if logr!=mp.ninf else mp.mpf(0)
            W=max(2*c,peak);lower=W-mp.log(2*c)-2
            must(max(logbulk,peak)>=lower-mp.mpf('1e-120'),'R16 lower witnesses')
            for L in map(mp.mpf,['0','.001','.5','1.5','1.999999','2']):
                for theta in map(mp.mpf,['0','.0001','.2','.5','.9999','1']):
                    must(scalar_log(c,logr,L,theta)<=W+mp.log(2)+mp.mpf('1e-120'),'R16 upper all tested points')
                    count+=1
    stats['scalar_bracket_sample_cases']=count
    reject('omit-linear-Taylor-term',Q(101,100)**2<=1+9*Q(1,100)**2,{'v':1,'p':'1/100','alpha':2})
    reject('drop-peak-exponential-from-remainder',3**10-1-20<=4,{'v':1,'p':2,'alpha':10})
    D=25;alpha=mp.mpf(20);groups=[(Q(3,2),12),(Q(1),13)]
    trace=sum(x*n for x,n in groups)
    unnormalized=(stable_sum_log([(x,n,alpha) for x,n in groups])-mp.log(D))/(alpha-1)
    actual=entropy_from_raw(groups,alpha)
    reject('omit-exact-trace-normalization',mp.almosteq(unnormalized,actual),{'raw_deficit':str(unnormalized),'actual':str(actual),'trace':str(trace),'D':D})
    reject('use-floor-without-rank-conditions',int(mp.floor(mp.mpf(9)/20))>=1,{'m':3,'D':9,'alpha_t':20,'rank':0})
    # A relaxed continuous rank is not a physical projection rank.
    reject('replace-integer-rank-by-real-D-over-width',Q(25,3).denominator==1,{'D':25,'alpha_t':3,'fractional_rank':'25/3','physical_floor_rank':8})
    m=10;D=m*m;alpha=mp.mpf(D*D);u=mp.mpf(3)*D/(D+2)
    # Exact endpoint bounds every true moment by u^(alpha-1), whereas F*>=3^alpha/D.
    logratio=alpha*mp.log(3)-mp.log(D)-(alpha-1)*mp.log(u)
    reject('promote-entropy-profile-to-unrestricted-relative-moment',logratio<=mp.log(2),{'m':m,'D':D,'alpha':str(alpha),'log_lower_bound_F_over_Mstar':str(logratio)})
    # The sum of finite error terms need not pointwise improve the old bound.
    m=3;D=9;a=mp.mpf(999999)
    new=mp.log(27)/a+4*mp.mpf(m)/(D-m)
    old=2*mp.mpf(m)/(D-m)+(2*mp.log(a)+mp.log(48)+2)/a
    reject('new-upper-error-pointwise-dominates-old',new<=old,{'m':m,'D':D,'alpha':str(a+1),'new_error':str(new),'old_error':str(old),'kind':'wording-scope witness; both theorem inequalities can remain true'})
    stats['expected_rejections']=len(rejections)
    result={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_manifest_sha256':hashlib.sha256((base/'INPUT_MANIFEST.json').read_bytes()).hexdigest(),'counts':stats,'rejected':rejections,'author_code_executed':False,'reviewer_written':True,'finite_diagnostics_only':True,'full_feasible_optimization_numerically_certified':False,'arbitrary_depth_or_unbounded_quantifiers_computer_proved':False,'Lean':False,'precision':mp.mp.dps}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'run':str(out),'status':'PASS','counts':stats}))
except Exception:
    (out/'RESULT.json').write_text(json.dumps({'status':'FAIL','utc':datetime.now(timezone.utc).isoformat(),'counts_before_failure':stats,'traceback':traceback.format_exc()},indent=2)+'\n')
    raise
