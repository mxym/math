"""Fresh reviewer code. Sparse integer multiplicities; no author imports."""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as Q
from math import comb
import hashlib,json,shutil,traceback
import mpmath as mp
import sympy as sp

mp.mp.dps=400
base=Path(__file__).resolve().parent
out=base/'runs'/datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out.mkdir(parents=True,exist_ok=False)
shutil.copyfile(__file__,out/'independent_checks.py')
shutil.copyfile(base/'INPUT_MANIFEST.json',out/'INPUT_MANIFEST.json')
counts={};rejected=[]
def must(condition,label):
    if not condition:raise AssertionError(label)
def reject(name,incorrect_assertion,detail):
    try:must(incorrect_assertion,name)
    except AssertionError as e:
        row={'name':name,'status':'REJECTED','actual_exception':repr(e),'detail':detail}
        rejected.append(row);(out/('REJECTED-'+name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    else:raise AssertionError('false variant survived '+name)
def real(x):
    return mp.mpf(x.numerator)/x.denominator if isinstance(x,Q) else mp.mpf(x)
def merge(groups):
    d={}
    for x,n in groups:
        if n:d[x]=d.get(x,0)+n
    return sorted(d.items(),reverse=True)
def normalize(raw):
    D=sum(n for x,n in raw);trace=sum(x*n for x,n in raw)
    return merge([(Q(D)*x/trace,n) for x,n in raw])
def trim(groups,left,right):
    position=1;ans=[]
    for x,n in groups:
        overlap=max(0,min(position+n-1,right)-max(position,left)+1)
        if overlap:ans.append((x,overlap))
        position+=n
    return ans
def parameters(m,groups):
    D=sum(n for x,n in groups);R=m*(m-1)//2;K=m*(m+1)//2;j=D-K+1
    mid=trim(groups,R,j);N=sum(n for x,n in mid)
    must(N==D-m*m+2,'inclusive exact middle count')
    A=mid[-1][0];B=mid[0][0];mu=sum(x*n for x,n in mid)/N
    kappa=B/A-1;L=(m-1)*kappa
    theta=(mu/A-1)/kappa if kappa else Q(0)
    eta=2*(m-2)*kappa*kappa/(2-(m-3)*kappa)
    return D,N,mid,A,kappa,L,theta,eta
def exact_loss(m,groups,alpha):
    D,N,mid,A,kappa,L,theta,eta=parameters(m,groups)
    must(0<=L<=2 and 0<=theta<=1,'closed actual parameter interval')
    M=sum(x**alpha*n for x,n in groups)/D
    midM=sum(x**alpha*n for x,n in mid)/D
    top=groups[0][0]
    P=(A**alpha*(3-eta)**alpha-top**alpha)/D
    T=M-midM-top**alpha/D
    # Chord gap from positive binomial coefficients, not subtraction of its chord.
    C=Q(0);J=Q(0);rounded_upper=Q(0);transport_cost=Q(0)
    if kappa:
        for x,n in mid:
            u=(x/A-1)/kappa;z=L*u
            C+=Q(n,D)*A**alpha*sum(Q(comb(alpha,j))*kappa**j*(u-u**j) for j in range(2,alpha+1))
            J+=Q(n,N)*z*(L-z)
            rounded_upper+=Q(n,N)*u
            transport_cost+=Q(n,N)*((1-u)*z+u*(L-z))
        must(rounded_upper==theta,'endpoint coupling preserves exact mean')
        must(transport_cost==2*J/L,'explicit endpoint transport coupling')
    lead=Q(N,D)*A**alpha*(1+theta*((1+kappa)**alpha-1))+A**alpha*(3-eta)**alpha/D
    must(C>=0 and J>=0 and P>=0 and T>=0,'all exact nonnegative losses')
    must(M==lead-C-P+T,'exact independent loss identity')
    must((C==0)==(J==0),'strict chord equality')
    low=Q(alpha*(alpha-1),2*(m-1)**2)*Q(N,D)*A**alpha*J
    must(low<=C<=low*(1+kappa)**(alpha-2),'explicit curvature bounds')
    return {'D':D,'N':N,'C':C,'J':J,'P':P,'T':T,'M':M,'lead':lead,'L':L,'theta':theta}
def protected(m,D,L,h):
    kappa=Q(1,m*m) if L==0 else L/(m-1)
    eta=2*(m-2)*kappa*kappa/(2-(m-3)*kappa)
    d=2-kappa-eta;must(d>=0,'actual Schmidt protection coefficient')
    # h is a rational target, so nearest rank and clipping are exact integers.
    target=h*D;k=(2*target.numerator+target.denominator)//(2*target.denominator)
    k=max(m**3,min(D-m**3,k));must(1<=k<D,'physical clipped rank')
    raw=[(3-eta,1),(1+kappa,k-1),(Q(1),D-k)]
    return normalize(raw),k,kappa,eta,d
def log_moment(groups,alpha):
    D=sum(n for x,n in groups)
    values=[mp.log(n)+alpha*mp.log(real(x)) for x,n in groups if x>0 and n]
    top=max(values)
    return top+mp.log(mp.fsum(mp.exp(x-top) for x in values))-mp.log(D)

try:
    K,h,C0=sp.symbols('K h C0',real=True)
    bulk=sp.exp(-K*h)*(1+h*(sp.exp(K)-1))
    must(sp.simplify(sp.diff(bulk,K)-h*(1-h)*sp.exp(-K*h)*(sp.exp(K)-1))==0,'strict bulk width derivative')
    c=sp.symbols('c',positive=True)
    hc=1/(2*c)-1/(sp.exp(2*c)-1)
    must(sp.simplify(sp.diff(bulk,h).subs({K:2*c,h:hc}))==0,'pure-bulk stationary fraction')
    mu,kappa,eta=sp.symbols('mu kappa eta',real=True)
    # First-order peak coefficient with mu=1+o(1/m).
    eps,l,z=sp.symbols('eps l z',real=True)
    target=(1/(1+l*z*eps))*(3-2*l*l*eps/(2-l))
    must(sp.simplify(-sp.diff(target,eps).subs(eps,0)-(3*l*z+2*l*l/(2-l)))==0,'interior peak correction')
    counts['symbolic_identities']=3
    cases=0;transport_cases=0;lossyC=None;lossyP=None
    for m,n in [(3,3),(3,9),(4,13),(5,5),(5,17),(7,23)]:
        D=m*n;t=Q(2,m-1)
        raws=[[(Q(1),D)],[(Q(3),1),(Q(1),D-1)]]
        for width in [t/4,t/2,t]:
            eta0=2*(m-2)*width**2/(2-(m-3)*width)
            a=D//5;b=D//4;low=D-1-a-b
            raws.append([(3-eta0,1),(1+width,a),(1+width/2,b),(Q(1),low)])
            for rank in [1,D//3,D-1]:
                raws.append([(3-eta0,1),(1+width,rank-1),(Q(1),D-rank)])
            # A full contraction, no spike, is also actual APPT and leaves peak slack.
            raws.append([(1+width,a),(1+width/2,b),(Q(1),D-a-b)])
        for raw in raws:
            groups=normalize(raw)
            must(sum(x*n for x,n in groups)==D,'exact trace')
            for alpha in [2,4,7,11]:
                row=exact_loss(m,groups,alpha);cases+=1
                if row['L']:transport_cases+=1
                if row['C']>0:lossyC=row
                if row['P']>0:lossyP=row
    must(lossyC is not None and lossyP is not None,'both nonzero loss types exercised')
    counts['exact_sparse_physical_loss_cases']=cases
    counts['exact_mean_preserving_endpoint_couplings']=transport_cases
    count=0
    attain=[]
    for m in [10,20,50,100]:
        D=m*((3**m+m-1)//m)
        for L in [Q(0),Q(1,3),Q(1),Q(2)]:
            for h0 in [Q(0),Q(2,5),Q(1)]:
                groups,k,width,eta0,d=protected(m,D,L,h0)
                row=exact_loss(m,groups,3)
                must(row['L']==(m-1)*width,'actual width equals intended width')
                must(row['J']==row['C']==row['P']==0,'actual saturated endpoint family')
                D0,N,mid,A,kappa0,L0,theta0,et=parameters(m,groups)
                R=m*(m-1)//2
                must(theta0==Q(k-R+1,N),'actual middle fraction after rank clipping')
                attain.append({'m':m,'D':str(D),'target_L':str(L),'target_h':str(h0),'actual_L':str(row['L']),'actual_theta':str(row['theta']),'rank_integer':str(k)})
                count+=1
    counts['exact_clipped_rank_and_redundant_theta_cases']=count
    # Noninteger real-order chord curvature, using aggregate actual middle values.
    count=0
    m=20;D=m*((3**m+m-1)//m);t=Q(2,m-1)
    groups=normalize([(Q(1)+t,D//4),(Q(1)+t/3,D//3),(Q(1),D-D//4-D//3)])
    D,N,mid,A,kappa0,L0,theta0,eta0=parameters(m,groups)
    J=sum(real(Q(n,N)*(m-1)*(x/A-1)*(L0-(m-1)*(x/A-1))) for x,n in mid)
    for alpha in map(mp.mpf,['2.001','5.25','19.5','40.125','100.75']):
        chord=mp.fsum(real(Q(n,D))*real(A)**alpha*(1+real((x/A-1)/kappa0)*(real(1+kappa0)**alpha-1)-real(x/A)**alpha) for x,n in mid)
        lower=alpha*(alpha-1)/(2*(m-1)**2)*real(Q(N,D))*real(A)**alpha*J
        must(lower<=chord+mp.mpf('1e-300') and chord<=lower*real(1+kappa0)**(alpha-2)+mp.mpf('1e-300'),'real-order curvature comparison')
        count+=1
    counts['real_order_chord_cases']=count
    # Moving-window examples are diagnostics; they do not certify every optimizer.
    geometry=[];bulkrows=[]
    c0=mp.mpf(1);hbulk=mp.mpf('.5')-1/mp.expm1(2)
    logF=mp.log(mp.expm1(2)/2)-1+2/mp.expm1(2)
    for m in [20,60,180]:
        alpha=mp.mpf(m);D=m*((3**m+m-1)//m)
        groups,k,w,eta0,d=protected(m,D,Q(1),Q(3,10))
        peak=real(groups[0][0]);geometry.append({'m':m,'m_times_peak_gap':str(m*(3-peak)),'interior_limit':'2.9'})
        D=m*((9**m+m-1)//m);rank=int(mp.floor(hbulk*D))
        for label,L in [('projection',mp.mpf(2)),('protected',2-1/mp.sqrt(m))]:
            width=L/(m-1);eta0=2*(m-2)*width**2/(2-(m-3)*width);d=2-width-eta0
            z0=1+width*mp.mpf(rank)/D+d/D
            top=(3-eta0)/z0
            rows=[((3-eta0)/z0,1),((1+width)/z0,rank-1),(1/z0,D-rank)]
            values=[mp.log(n)+alpha*mp.log(x) for x,n in rows if n]
            vmax=max(values);logM=vmax+mp.log(mp.fsum(mp.exp(v-vmax) for v in values))-mp.log(D)
            bulkrows.append({'m':m,'type':label,'top':str(top),'logM':str(logM),'logF_bulk':str(logF),'actual_rank':str(rank),'L':str(L)})
    counts['moving_window_geometry_cases']=len(geometry)+len(bulkrows)
    reject('omit-middle-spread-loss',lossyC['M']==lossyC['lead']-lossyC['P']+lossyC['T'],{'actual_C':str(lossyC['C'])})
    reject('omit-actual-peak-slack',lossyP['M']==lossyP['lead']-lossyP['C']+lossyP['T'],{'actual_P':str(lossyP['P'])})
    m=5;D=625;t=Q(2,m-1);groups=normalize([(1+t,D//2),(Q(1),D-D//2)])
    _,_,_,_,width,L0,_,_=parameters(m,groups)
    reject('use-m-kappa-as-closed-width',m*width<=2,{'actual_closed_L':str(L0),'m_kappa':str(m*width)})
    m=10;D=m*((3**m+m-1)//m);w=Q(1,m-1);eta0=2*(m-2)*w*w/(2-(m-3)*w)
    rankone=normalize([(3-eta0,1),(Q(1),D-1)])
    _,_,_,_,wa,La,ha,_=parameters(m,rankone)
    reject('nominal-width-survives-rank-one-middle',wa==w,{'nominal_width':str(w),'actual_width':str(wa),'actual_L':str(La),'actual_theta':str(ha)})
    pole=normalize([(Q(3),1),(Q(1),D-1)])
    _,_,_,_,wa,La,ha,_=parameters(m,pole)
    reject('exact-pole-realizes-nonzero-redundant-theta',ha==Q(2,5),{'actual_pole_theta':str(ha),'required_redundant_limit':'2/5','remedy':'use positive width1/m^2, checked separately'})
    # Deliberately NON-APPT toy: a vanishing atom of height4 can carry a unit moment.
    m=40;D=m*((4**m+m-1)//m);head=mp.power(4,m)/D
    reject('weak-law-alone-controls-unbounded-exponential',head<mp.mpf('.5'),{'toy_peak':4,'physical_APPT_cap_less_than':3,'head_moment':str(head),'bulk_weak_mass_of_atom':str(mp.mpf(1)/D),'not_a_counterexample_to_actual_theorem':True})
    projection=bulkrows[-2];spiked=bulkrows[-1]
    must(abs(mp.mpf(projection['logM'])-logF)<mp.mpf('.1') and abs(mp.mpf(spiked['logM'])-logF)<mp.mpf('.1'),'two near-bulk moment diagnostics')
    reject('same-limiting-bulk-forces-same-outlier',abs(mp.mpf(projection['top'])-mp.mpf(spiked['top']))<mp.mpf('.5'),{'projection_top':projection['top'],'protected_top':spiked['top'],'same_limiting_bulk_parameters':'L->2,theta->h_c; written limit proof required','finite_example_only':True})
    (out/'GEOMETRY.json').write_text(json.dumps({'attainment':attain,'interior':geometry,'two_bulk_families':bulkrows},indent=2)+'\n')
    result={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_manifest_sha256':hashlib.sha256((base/'INPUT_MANIFEST.json').read_bytes()).hexdigest(),'counts':counts,'expected_rejections':rejected,'author_code_imported_or_executed':False,'reviewer_written':True,'finite_diagnostics_not_full_optimizer_proof':True,'Lean':False,'mpmath_precision':mp.mp.dps}
    (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','run':str(out),'counts':counts,'rejections':len(rejected)}))
except Exception:
    (out/'RESULT.json').write_text(json.dumps({'status':'FAIL','utc':datetime.now(timezone.utc).isoformat(),'counts_before_failure':counts,'traceback':traceback.format_exc()},indent=2)+'\n')
    raise
