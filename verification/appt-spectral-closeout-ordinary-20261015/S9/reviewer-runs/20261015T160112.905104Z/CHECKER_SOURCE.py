"""Independent S9 diagnostics, written without importing author helpers.

Exact compressed integer-multiplicity spectra, stable real-power kernels, and
deliberately false variants.  Finite controls supplement the mathematical
reading; none certifies the all-state theorem or evaluates the actual maximum.
"""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import contextlib, hashlib, json, platform, sys, traceback
import mpmath as mp
import sympy as sy

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'owner-snapshot/worktree/research/breadth-tcs-20261015/phase-9-diverging-physical-reduction'
mp.mp.dps = 420
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def merge(rows):
    out = {}
    for y, k in rows:
        assert k >= 0
        if k:
            out[F(y)] = out.get(F(y), 0) + k
    return sorted(out.items(), reverse=True)


def spectra(m, n):
    D = m*n
    c = F(2, m-1)
    yield 'uniform', [(F(1), D)]
    for k in sorted({1, D//7, D//2, D-1}):
        scale = F(D, 1)/(D+c*k)
        yield 'projection-'+str(k), merge([((1+c)*scale, k), (scale, D-k)])
    for c1 in [F(2), F(3, 2)]:
        scale = F(D, 1)/(D+c1)
        yield 'pole-'+str(c1), merge([((1+c1)*scale, 1), (scale, D-1)])
    yield 'singular-hole', [(F(D, D-1), D-1), (F(0), 1)]
    if D % 4 == 0:
        # I+Y with 0<=Y<=2/(m-1) I; after normalization endpoints 1+-1/m.
        yield 'three-level', [(1+F(1,m), D//4), (F(1), D//2), (1-F(1,m), D//4)]


def pieces(m, n, rows):
    D=m*n
    R=m*(m-1)//2
    j=D-m*(m+1)//2+1
    N=D-m*m+2
    assert R<=j and j-R+1==N
    assert sum(k for y,k in rows)==D
    assert sum(y*k for y,k in rows)==D
    middle=[]; exceptional=[]; start=1
    for y,k in rows:
        count=max(0, min(start+k-1,j)-max(start,R)+1)
        middle.append((y,count))
        exceptional.append((y,k-count-(1 if start==1 else 0)))
        start += k
    assert all(k>=0 for y,k in exceptional)
    middle=[(y,k) for y,k in middle if k]
    exceptional=[(y,k) for y,k in exceptional if k]
    assert sum(k for y,k in middle)==N
    return D,N,middle,exceptional


def exact_case(m,n,a,rows):
    D,N,mid,other=pieces(m,n,rows)
    H=lambda y:y**a-1-a*(y-1)
    M=sum(k*y**a for y,k in rows)/D
    peak=H(rows[0][0])
    middle=sum(k*H(y) for y,k in mid)
    remainder=sum(k*H(y) for y,k in other)
    A=mid[-1][0]; top=mid[0][0]
    assert A>0
    mu=sum(k*y for y,k in mid)/N
    kap=top/A-1
    theta=(mu/A-1)/kap if kap else F(0)
    zk=(1+kap)**a-1
    if kap:
        assert theta>0 and theta<1
        lam=(N*(1+theta*zk)-sum(k*(y/A)**a for y,k in mid))/(N*theta*zk)
    else:
        lam=F(1)
    bracket=A**a*(1+theta*zk*(1-lam))-1-a*(mu-1)
    C=1+(peak+N*bracket)/D
    QE=(rows[0][0]-1)**2 + sum(k*(y-1)**2 for y,k in other)
    assert 0<=kap<=F(2,m-1) and 0<=theta<=1 and 0<=lam<=1
    assert bracket==middle/N and bracket>=0
    assert D*(M-1)==sum(k*H(y) for y,k in rows)
    assert M-C==remainder/D>=0
    assert remainder<=3*a*a*QE*(1+peak)
    assert C>=1 and M/C<=1+3*a*a*QE
    return dict(M=M,C=C,N=N,mu=mu,kap=kap,theta=theta,lam=lam,
                zk=zk,peak=peak,bracket=bracket,remainder=remainder,QE=QE)


def asmp(q):
    return mp.mpf(q.numerator)/q.denominator if isinstance(q,F) else mp.mpf(q)


def kernel(y,a):
    if not y:
        return a-1
    return mp.expm1(a*mp.log(y))-a*(y-1)


def real_case(m,n,a,rows):
    a=mp.mpf(a)
    D,N,mid,other=pieces(m,n,rows)
    hp=kernel(asmp(rows[0][0]),a)
    hb=sum(k*kernel(asmp(y),a) for y,k in mid)
    re=sum(k*kernel(asmp(y),a) for y,k in other)
    # Evaluate log differences without subtracting nearby large logarithms.
    C=1+(hp+hb)/D
    delta=mp.log1p(re/(D*C))
    u=mp.mpf(3)*D/(D+2); t=mp.mpf(D)/(D+2)
    esp=(kernel(u,a)+(D-1)*kernel(t,a))/D
    chi=a*mp.log(u)-mp.log(D)
    r=mp.exp(chi)
    assert esp>=r/2 and C>=1 and re>=0
    qE=asmp((rows[0][0]-1)**2+sum(k*(y-1)**2 for y,k in other))
    assert re<=3*a*a*qE*(1+hp)*(1+mp.mpf('1e-80'))
    assert re/(D*esp)<=256*a*a*(mp.mpf(15)/16)**a
    logerr=delta/mp.log1p(esp)
    upper=10000*(a*a*(mp.mpf(15)/16)**(a/2)+mp.log1p(a)/a)
    assert 0<=logerr<=upper
    eta=mp.log(mp.mpf(16)/15)
    regime='tiny' if chi<=0 else ('middle' if chi<=eta*a/2 else 'large')
    return {'m':m,'D_digits':len(str(D)),'alpha':mp.nstr(a,16),'regime':regime,
            'chi':mp.nstr(chi,16),'relative_excess_omission_vs_actual_spike':mp.nstr(re/(D*esp),12),
            'relative_log_omission_vs_actual_spike':mp.nstr(logerr,12)}


def reject(run,name,fn,explanation):
    p=run/'rejected-variants'/name
    p.mkdir(parents=True)
    try:
        fn()
    except AssertionError:
        (p/'stderr.txt').write_text(traceback.format_exc())
        return {'variant':name,'status':'REJECTED_BY_ACTUAL_ASSERTION_ERROR','meaning':explanation}
    raise RuntimeError('False variant was not rejected: '+name)


def main(run):
    assert sha(SOURCE/'PAPER.md')=='812ba384981a4ed6ae1ae62d93723fc0505609b7ecf7997c452331947ffcb078'
    # Recheck the frozen private inputs without overwriting the earlier receipt.
    old=json.loads((ROOT/'INPUT_VERIFICATION.json').read_text())
    for row in old['files']:
        p=SOURCE/row['path']
        assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
    assert sha(ROOT/'owner.zip')==old['owner_zip_sha256']
    symbolic=[]
    x=sy.symbols('x',nonnegative=True)
    for a in range(2,11):
        quotient=sy.Poly(sy.cancel(((1+x)**a-1-a*x)/x**2),x)
        assert all(c>0 for c in quotient.all_coeffs())
        derivative=sy.Poly(sy.diff(quotient.as_expr(),x),x)
        assert derivative.is_zero or all(c>=0 for c in derivative.all_coeffs())
        symbolic.append({'alpha':a,'kernel_quotient_coefficients':str(quotient.as_expr())})
    b,th,z,l,mu,a,N=sy.symbols('b th z l mu a N')
    centered=sy.expand(N*(b*(1+th*z*(1-l))-1-a*(mu-1)))
    assert sy.expand(centered-(N*b+N*b*th*z-N*b*th*z*l-N-N*a*(mu-1)))==0
    symbolic.append({'identity':'exact chord/mean/linear centering, including prefactors'})
    exact=[]
    cache={}
    for m in [4,6,10]:
        for n in [m,m*m]:
            for name,rows in spectra(m,n):
                for order in [2,3,7,m*n+1]:
                    q=exact_case(m,n,order,rows)
                    cache[(m,n,name,order)]=q
                    exact.append({'m':m,'n':n,'alpha':order,'family':name,
                                  'constant_middle':q['kap']==0,'nonzero_chord':bool(q['lam'] and q['theta'])})
    # All three chi regimes, including real alpha and alpha much greater than D.
    real=[]
    m=2048
    eta=mp.log(mp.mpf(16)/15)
    for order in [mp.mpf('64.25'),mp.mpf('128.5'),mp.mpf('256.125')]:
        ia=int(mp.ceil(order))
        ns=[m*3**(2*ia), int(mp.ceil(mp.exp(order*mp.log(3)-eta*order/4)/m)), m]
        for n in ns:
            for name,rows in spectra(m,n):
                real.append(dict(real_case(m,n,order,rows),family=name))
    for order in [mp.mpf(m),mp.mpf(m*m)*2,mp.mpf(m*m)**2+mp.mpf('0.375')]:
        for name,rows in spectra(m,m):
            real.append(dict(real_case(m,m,order,rows),family=name))
    assert {q['regime'] for q in real}=={'tiny','middle','large'}
    # Actual APPT three-level path, alpha=o(m), with vanishing Lambda but a
    # persistent factor two error at the first nonzero excess if it is dropped.
    chord=[]
    for k in [4,8,16,32]:
        m=k*k; n=m*3**(2*k); D=m*n
        rows=dict(spectra(m,n))['three-level']
        q=exact_case(m,n,k,rows)
        u=mp.mpf(3)*D/(D+2)
        benchmark=mp.exp(k*mp.log(u)-mp.log(D))+mp.mpf(k*(k-1))/(2*m*m)
        wrong=q['C']+q['N']*(q['mu']/(1+q['kap']*q['theta']))**k*q['theta']*q['zk']*q['lam']/D
        goodratio=asmp(q['M']-1)/benchmark
        badratio=asmp(wrong-1)/benchmark
        assert mp.mpf('.49')<goodratio<mp.mpf('.52')
        assert mp.mpf('.90')<badratio<mp.mpf('1.01')
        chord.append({'k':k,'m':m,'alpha':k,'actual_lambda':mp.nstr(asmp(q['lam']),18),
                      'actual_excess_over_asymptotic_scale':mp.nstr(goodratio,18),
                      'omitted_lambda_excess_over_asymptotic_scale':mp.nstr(badratio,18)})
    assert asmp(cache[(4,16,'pole-2',3)]['mu'])<1
    wrongs=[]
    q=cache[(4,16,'three-level',7)]
    wrongs.append(reject(run,'omit-actual-chord-loss',lambda:assert_equal(q['M'],q['C']+q['remainder']/(4*16)+q['N']*(q['mu']/(1+q['kap']*q['theta']))**7*q['theta']*q['zk']*q['lam']/(4*16)),
                         'Actual three-level APPT body is not the endpoint chord.'))
    q=cache[(4,16,'pole-2',3)]
    wrongs.append(reject(run,'zero-width-implies-unit-mean',lambda:assert_equal(q['mu'],F(1)),
                         'An actual pure-spike state has constant middle mu=D/(D+2)<1.'))
    wrongs.append(reject(run,'zero-width-implies-zero-centered-body',lambda:assert_equal(q['bracket'],F(0)),
                         'H(mu)>0 even when actual middle width is zero.'))
    wrongs.append(reject(run,'omit-linear-mean-centering',lambda:assert_equal(q['bracket'],q['bracket']+3*(q['mu']-1)),
                         'The trace-centered body term cannot discard alpha(mu-1).'))
    q=cache[(4,16,'singular-hole',3)]
    wrongs.append(reject(run,'discard-nonleading-exceptionals-exactly',lambda:assert_equal(q['remainder'],F(0)),
                         'The negative-hole kernel is nonzero; only a scale-controlled omission is justified.'))
    D=mp.mpf(4096); order=D**2
    wrongs.append(reject(run,'replace-exact-peak-base-by-three',lambda:assert_small(order*mp.log1p(2/D),mp.mpf('0.01')),
                         'For alpha=D^2 the logarithmic ratio (3/u_D)^alpha diverges, not tends to zero.'))
    m=10000; D=m*m; order=mp.mpf(m); coeff=2-1/mp.sqrt(order)
    top=mp.mpf(D)*(1+coeff)/(D+coeff)
    exactcap=mp.mpf(3)*D/(D+2)
    h=order*mp.log(exactcap/top)
    chi=order*mp.log(exactcap)-mp.log(D)
    assert h/chi<mp.mpf('.004') and mp.exp(-h)<mp.mpf('1e-14')
    wrongs.append(reject(run,'log-optimality-forces-sharp-moment',lambda:assert_small(h,mp.mpf('0.01')),
                         'Actual positive pole density with coefficient 2-1/sqrt(alpha): tiny relative logarithmic peak loss coexists with vanishing sharp peak ratio. Finite diagnostics supplement the analytic path.'))
    return {'status':'PASS','paper_sha256':sha(SOURCE/'PAPER.md'),'symbolic_controls':symbolic,
            'exact_compressed_spectra':exact,'stable_real_order_controls':real,'vanishing_chord_loss_actual_states':chord,
            'rejected_variants':wrongs,'author_code_executed':False,
            'limitations':'No finite sample certifies all APPT states, computes M*, proves a universal constant, or replaces the full mathematical argument. Asymptotic benchmark in chord diagnostics is not finite exact M*.'}


def assert_equal(a,b):
    assert a==b, 'deliberately false equality rejected'


def assert_small(a,b):
    assert abs(a)<=b, 'deliberately false smallness rejected'


if __name__=='__main__':
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    run=ROOT/'reviewer-runs'/stamp
    run.mkdir(parents=True)
    (run/'CHECKER_SOURCE.py').write_bytes(Path(__file__).read_bytes())
    receipt={'status':'RUNNING','utc_started':datetime.now(timezone.utc).isoformat(),
             'script_sha256':sha(Path(__file__)),'runtime':{'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sy.__version__,'mp_dps':mp.mp.dps}}
    try:
        with (run/'stdout.txt').open('w') as out, (run/'stderr.txt').open('w') as err, contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            result=main(run)
            print(json.dumps({'status':result['status'],'exact_cases':len(result['exact_compressed_spectra']),
                              'real_cases':len(result['stable_real_order_controls']),'wrong_variants':len(result['rejected_variants'])}))
        receipt.update(result)
    except BaseException as exc:
        receipt.update(status='FAIL',exception_type=type(exc).__name__,exception=str(exc),traceback=traceback.format_exc())
        (run/'unexpected-failure.txt').write_text(traceback.format_exc())
    receipt['utc_completed']=datetime.now(timezone.utc).isoformat()
    (run/'RESULT.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'run':str(run),'script_sha256':receipt['script_sha256'],
                      'exception':receipt.get('exception'),'traceback':receipt.get('traceback')},ensure_ascii=False))
    sys.exit(0 if receipt['status']=='PASS' else 1)
