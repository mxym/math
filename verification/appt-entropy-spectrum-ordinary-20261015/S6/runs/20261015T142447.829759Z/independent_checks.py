"""Independent S6 finite diagnostics, written here without author imports.

Universal assertions are reviewed in prose, not certified by these samples.
All compressed spectra used below are actual all-unitary APPT densities:
rho=(I+a vv*+s P)/(D+a+s k), P orthogonal to v, rank(P)=k,
a,s>=0 and a+(m-1)s<=2.  Every transformed partial transpose is
positive by the pure-state -1/2 bound and the projection -(m-1)/2 bound.
The proof of that sufficient bound is stated separately in REVIEW.md.
"""
from fractions import Fraction as F
from pathlib import Path
import datetime, hashlib, json, platform, subprocess, sys
import mpmath as mp
import sympy as sy

mp.mp.dps=800
ROOT=Path(__file__).resolve().parent

def rational_levels(m,n,a,k):
    D=m*n; a=F(a); s=(2-a)/(m-1)
    assert 0<=a<=2 and 0<=k<=D-1 and a+(m-1)*s==2
    Z=F(D)+a+s*k
    parts=[(F(D)*(1+a)/Z,1),(F(D)*(1+s)/Z,k),(F(D)/Z,D-k-1)]
    parts=[(y,c) for y,c in parts if c]
    parts.sort(reverse=True)
    assert sum(c for y,c in parts)==D
    assert sum(c*y for y,c in parts)==D
    return parts

def cv(x):
    if isinstance(x,F): return mp.mpf(x.numerator)/x.denominator
    return mp.mpf(x)

def interval_stat(parts,lo,hi,fun):
    start=1; total=mp.mpf(0)
    for y,c in parts:
        count=max(0,min(start+c-1,hi)-max(start,lo)+1)
        total+=count*fun(cv(y)); start+=c
    return total

def real_profile(m,n,alpha,a,k=0):
    D=m*n; alpha=cv(alpha); parts=rational_levels(m,n,a,k)
    y1=cv(parts[0][0]); u=mp.mpf(3)*D/(D+2)
    M=sum(c*cv(y)**alpha for y,c in parts)/D
    Tp=y1**alpha/D; r=u**alpha/D
    chi=mp.log(r); h=alpha*mp.log(u/y1)
    return dict(m=m,n=str(n),alpha=str(alpha),a=str(a),k=str(k),
                parts=parts,M=M,Tp=Tp,r=r,chi=chi,h=h,y1=y1,u=u,
                tail_ratio=(M-Tp)/Tp)

def paper_path(k):
    m=k*k; alpha=m
    n=int(mp.ceil(mp.mpf(3)**alpha*mp.exp(-k)/m))
    assert n>=m
    return real_profile(m,n,alpha,F(2)-F(3,k))

def wrong(name):
    if name=='omit_centering':
        p=rational_levels(5,7,F(3,2),4); D=35; A=4
        M=sum(c*y**A for y,c in p)/D
        assert D*(M-1)==sum(c*y**A for y,c in p), 'WRONG omit_centering'
    elif name=='finite_peak_identity':
        p=real_profile(32,32,8,2)
        assert p['M']/p['r']==mp.exp(-p['h']), 'WRONG finite_peak_identity'
    elif name=='entropy_implies_sharp_loss':
        p=real_profile(4096,4096,4096,F(2)-F(1,64))
        assert p['h']<1, 'WRONG entropy_implies_sharp_loss'
    elif name=='divide_loss_by_alpha':
        p=paper_path(32)
        assert p['h']/1024<mp.mpf('.04')
        assert mp.log(p['M'])/p['chi']>mp.mpf('.5'), 'WRONG divide_loss_by_alpha'
    elif name=='coarse_error_relative_to_peak':
        p=paper_path(32)
        assert p['M']/p['Tp']<mp.mpf('1.1'), 'WRONG coarse_error_relative_to_peak'
    elif name=='second_peak_controls_tail_sum':
        p=paper_path(16)
        tail=cv(p['parts'][-1][0]); ratio=(tail/p['y1'])**256
        assert ratio<mp.mpf('1e-100')
        assert p['tail_ratio']<mp.mpf('.1'), 'WRONG second_peak_controls_tail_sum'
    elif name=='forget_trace_normalization':
        D=35
        assert F(D)+F(3,2)==D, 'WRONG forget_trace_normalization'
    else: raise ValueError(name)

def main():
    utc=datetime.datetime.now(datetime.timezone.utc)
    run=ROOT/'runs'/utc.strftime('%Y%m%dT%H%M%S.%fZ'); run.mkdir(parents=True)
    source=Path(__file__).read_bytes(); (run/'independent_checks.py').write_bytes(source)
    counts={}; details={}
    y,D,A,T,S=sy.symbols('y D A T S', positive=True)
    centered=sy.expand((D+2*T+S)/(D+T)**2-1/D)
    assert sy.simplify(D**2*centered-(S-T*T/D)/(1+T/D)**2)==0
    assert sy.simplify(1+(y**A-1-A*(y-1)+A*(y-1))/D-(D-1+y**A)/D)==0
    assert sy.diff((1-sy.symbols('s'))*(1+sy.symbols('s')*(y-1)),y)!=0
    # Exact polynomial integral identity at all y, including y=0, for four orders.
    t=sy.symbols('t')
    for order in [2,3,5,8]:
        integ=order*(order-1)*(y-1)**2*sy.integrate((1-t)*(1+t*(y-1))**(order-2),(t,0,1))
        assert sy.expand(integ-(y**order-1-order*(y-1)))==0
    # Exact finite-budget algebra controlling g2 and the least tail.
    e,b=sy.symbols('e b', nonnegative=True)
    assert sy.expand((2-e+b)**2-(2-e)**2)==b*(4-2*e+b)
    counts['symbolic_identities']=7

    exact=0
    for m in [4,7,32,65]:
        for n in [m,2*m+1,10*m]:
            Dim=m*n
            for a in [F(0),F(1),F(3,2),F(2)]:
                for rank in [0,1,Dim//2,Dim-1]:
                    parts=rational_levels(m,n,a,rank)
                    for order in [2,5,11]:
                        M=sum(c*y**order for y,c in parts)/Dim
                        H=sum(c*(y**order-1-order*(y-1)) for y,c in parts)
                        assert Dim*(M-1)==H and M>=1
                        top=parts[0][0]
                        assert top<=F(3*Dim,Dim+2)
                        assert M>=top**order/Dim
                        assert sum(c*y**order for y,c in parts)-top**order>=0
                        exact+=1
    counts['exact_compressed_actual_state_order_cases']=exact

    # Direct finite inequality with the actual m-dependent constants, no fitted error.
    finite=0; max_slack=mp.mpf(0)
    for m in [64,256,1024]:
        for n in [m,3*m+1]:
            Dim=m*n
            nu=mp.mpf(1)/m+mp.mpf(2)/(m-1)
            delta=(mp.mpf(2)/(m-1)+nu)/(1-nu)
            Cm=(mp.sqrt(8+mp.mpf(4)/(m-1))+m*nu)**2/(1-nu)**2
            Hm=(2+mp.sqrt(m-1)*nu)**2/(1-nu)**2
            v=1+mp.sqrt(Hm/2); zeta=(mp.mpf(m)/(m-1))**2/(1-nu)**2
            assert delta*m<6 and zeta<2
            for order in [mp.mpf('7.5'),mp.mpf(m)/2,mp.mpf(m)*mp.mpf('1.25')]:
                C=2; K=9*C*C*mp.exp(6*C)
                aa=order*(order-1)/2
                for a in [F(0),F(3,2),F(2)]:
                    rank=Dim//2
                    p=real_profile(m,n,order,a,rank)
                    H=lambda y:y**order-1-order*(y-1)
                    R=m*(m-1)//2; j=Dim-m*(m+1)//2+1
                    RB=interval_stat(p['parts'],R,j,H)
                    RE=interval_stat(p['parts'],2,R-1,H)+interval_stat(p['parts'],j+1,Dim,H)
                    assert RB/Dim<=K
                    assert RE<=aa*Cm*v**(order-2)
                    lhs=abs(p['M']/p['r']-mp.exp(-p['h']))
                    rhs=(1+K)/p['r']+(1+2*order)/p['u']**order+aa*Cm*v**(order-2)/p['u']**order
                    assert lhs<=rhs*(1+mp.mpf('1e-650'))
                    max_slack=max(max_slack,lhs/rhs)
                    finite+=1
    counts['finite_all_state_bound_diagnostics']=finite
    details['largest_observed_lhs_over_proved_rhs']=mp.nstr(max_slack,18)

    # Actual exponential-ceiling path in the paper, not the author's rational substitute.
    paths=[]
    for k in [4,8,16,32]:
        p=paper_path(k)
        assert abs(p['chi']-k)<mp.mpf('.01') if k>=8 else True
        assert abs(p['h']-k-mp.mpf('.5'))<mp.mpf('.15')
        assert p['M']/p['Tp']>2
        paths.append({q:mp.nstr(p[q],25) for q in ['chi','h','y1','M','Tp','tail_ratio']})
    counts['actual_exponential_ceiling_paths']=len(paths); details['exponential_ceiling_paths']=paths
    separ=[]
    for k in [8,16,32,64]:
        m=k*k
        p=real_profile(m,m,m,F(2)-F(1,k))
        assert p['h']>mp.mpf(k)/3
        assert 0<mp.log(p['M'])/p['chi']<1
        separ.append({q:mp.nstr(p[q],20) for q in ['chi','h','M','r']})
    counts['actual_entropy_vs_moment_paths']=len(separ); details['entropy_vs_moment_paths']=separ

    names=['omit_centering','finite_peak_identity','entropy_implies_sharp_loss',
           'divide_loss_by_alpha','coarse_error_relative_to_peak',
           'second_peak_controls_tail_sum','forget_trace_normalization']
    bad=[]
    for name in names:
        p=subprocess.run([sys.executable,str(Path(__file__).resolve()),'--wrong',name],capture_output=True,text=True)
        (run/(name+'.stdout.txt')).write_text(p.stdout)
        (run/(name+'.stderr.txt')).write_text(p.stderr)
        assert p.returncode!=0 and 'AssertionError: WRONG '+name in p.stderr, (name,p.returncode,p.stderr)
        bad.append({'variant':name,'returncode':p.returncode,'actual_assertion_error':True})
    res={'status':'PASS','utc':utc.isoformat(),'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'scope':'Independent finite diagnostics and actual rejected false variants, not universal proof/Lean',
         'source_sha256':hashlib.sha256(source).hexdigest(),'paper_sha256':'2374564f1f2cd3c576c3528d8acfda3f9a729ae08f506621f930ed42b33fd227',
         'runtime':{'python':platform.python_version(),'sympy':sy.__version__,'mpmath':mp.__version__,'mp_dps':mp.mp.dps},
         'counts':counts,'details':details,'wrong_variants':bad,
         'author_code_imported_or_executed':False}
    (run/'RESULT.json').write_text(json.dumps(res,indent=2)+'\n')
    (ROOT/'LATEST_RUN.json').write_text(json.dumps({'run':str(run),'source_sha256':res['source_sha256']},indent=2)+'\n')
    print(json.dumps({'status':'PASS','run':str(run),'counts':counts,'rejected_variants':len(bad)},indent=2))

if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='--wrong': wrong(sys.argv[2])
    else: main()
