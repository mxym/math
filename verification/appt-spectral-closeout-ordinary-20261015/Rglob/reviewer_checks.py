"""Independent Rglob controls; no author imports or copied helper functions.

All spectra have actual integer multiplicities. Scalar comparisons diagnose
the analytic fixed-m proof and are not finite unknown-APPT optimizations.
The non-effective compactness constant is not numerically certified here.
"""
from pathlib import Path
from fractions import Fraction as F
from datetime import datetime, timezone
import contextlib, hashlib, json, platform, sys, traceback
import mpmath as mp
import sympy as sy

R=Path(__file__).resolve().parent
S=R/'owner-snapshot/all-dimension-diverging-spectral-reduction-20261015'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mp.mp.dps=300


def joined(raw):
    q={}
    for y,k in raw:
        assert k>=0 and y>=0
        if k:q[F(y)]=q.get(F(y),0)+k
    return sorted(q.items(),reverse=True)


def normalized(D,raw):
    rows=joined(raw)
    assert sum(k for y,k in rows)==D
    tr=sum(k*y for y,k in rows)
    assert tr>0
    return [(F(D)*y/tr,k) for y,k in rows]


def families(m,n):
    D=m*n;t=F(2,m-1)
    yield 'uniform',[(F(1),D)]
    yield 'pole',normalized(D,[(F(3),1),(F(1),D-1)])
    yield 'half-pole',normalized(D,[(F(2),1),(F(1),D-1)])
    yield 'singular-hole',normalized(D,[(F(1),D-1),(F(0),1)])
    for k in sorted({1,2,D//2,D-1}):
        yield 'projection-'+str(k),normalized(D,[(1+t,k),(F(1),D-k)])
    if D%4==0:
        yield 'three-level',normalized(D,[(1+t,D//4),(1+t/2,D//2),(F(1),D//4)])


def split(m,n,rows):
    D=m*n;lo=max(2,m*(m-1)//2);hi=D-m*(m+1)//2+1
    N=hi-lo+1
    assert N==(D-m*m+2 if m>=3 else D-3) and N>=1
    assert sum(k for y,k in rows)==sum(k*y for y,k in rows)==D
    pos=1;body=[];removed=[]
    for y,k in rows:
        inside=max(0,min(hi,pos+k-1)-max(lo,pos)+1)
        outside=k-inside-(1 if pos==1 else 0)
        if inside:body.append((y,inside))
        if outside:removed.append((y,outside))
        pos+=k
    assert sum(k for y,k in body)==N
    assert sum(k for y,k in removed)+N+1==D
    A=body[-1][0];assert A>0
    mu=sum(k*y for y,k in body)/N
    width=body[0][0]/A-1
    theta=(mu/A-1)/width if width else F(0)
    QE=(rows[0][0]-1)**2+sum(k*(y-1)**2 for y,k in removed)
    u=F(3*D,D+2)
    assert 1<=rows[0][0]<=u
    if m==2:
        assert sum(k for y,k in removed)==2
        assert max(y for y,k in removed)<=F(D,D-1)
        assert max(y for y,k in removed)/u<=F(2,3)
    else:
        y2=rows[0][0] if rows[0][1]>1 else rows[1][0]
        assert (y2/A-1)**2<=2 and A<=F(D,hi)
    return dict(D=D,N=N,body=body,removed=removed,A=A,mu=mu,width=width,theta=theta,QE=QE,u=u)


def exact(m,n,p,rows):
    z=split(m,n,rows);D=z['D'];N=z['N'];A=z['A'];th=z['theta'];kap=z['width']
    H=lambda y:y**p-1-p*(y-1)
    M=sum(k*y**p for y,k in rows)/D
    hp=H(rows[0][0]);hb=sum(k*H(y) for y,k in z['body'])
    re=sum(k*H(y) for y,k in z['removed'])
    Zk=(1+kap)**p-1
    lam=1-(sum(k*(y/A)**p for y,k in z['body'])/N-1)/(th*Zk) if kap else F(1)
    bracket=A**p*(1+th*Zk*(1-lam))-1-p*(z['mu']-1)
    K=1+(hp+N*bracket)/D
    assert 0<=lam<=1 and bracket==hb/N>=0
    assert M-K==re/D>=0 and K>=1
    assert re<=3*p*p*z['QE']*(1+hp)
    assert M/K<=1+3*p*p*z['QE']
    return dict(z,M=M,K=K,hp=hp,hb=hb,re=re,lam=lam,bracket=bracket)


def mm(v):
    return mp.mpf(v.numerator)/v.denominator if isinstance(v,F) else mp.mpf(v)


def H(y,p):
    return p-1 if y==0 else mp.expm1(p*mp.log(y))-p*(y-1)


def real_case(m,n,p,rows):
    z=split(m,n,rows);D=z['D'];p=mp.mpf(p)
    hp=H(mm(rows[0][0]),p)
    hb=sum(k*H(mm(y),p) for y,k in z['body'])
    re=sum(k*H(mm(y),p) for y,k in z['removed'])
    K=1+(hp+hb)/D
    gap=mp.log1p(re/(D*K))
    qE=mm(z['QE'])
    assert re>=0 and K>=1
    assert re<=3*p*p*qE*(1+hp)*(1+mp.mpf('1e-100'))
    assert gap<=mp.log1p(3*p*p*qE)+mp.mpf('1e-100')
    if p>=64:
        u=mm(z['u']);t=mp.mpf(D)/(D+2)
        r=mp.exp(p*mp.log(u)-mp.log(D))
        esp=(H(u,p)+(D-1)*H(t,p))/D
        assert esp>=r/2
        v=max([mp.mpf(1)]+[mm(y) for y,k in z['removed']])
        rho=v/u
        assert 0<rho<1
        assert re/(D*esp)<=2*p*p*qE*rho**p*(1+mp.mpf('1e-90'))
        error=mp.nstr(gap/mp.log1p(esp),15)
    else:error=None
    return {'m':m,'D':D,'alpha':mp.nstr(p,18),'actual_spike_log_normalized_omission':error,
            'interpretation':'local sample gap only; not an effective universal compactness constant'}


def logmoment(q,p,theta):
    return mp.log1p(theta*mp.expm1(p*mp.log(q)))-p*mp.log1p((q-1)*theta)


def continuous(q,p):
    t=q-1;B=mp.expm1(p*mp.log(q))
    th=1/(t*(p-1))-p/((p-1)*B)
    assert 0<th<1
    return logmoment(q,p,th),th


def logsum(a,b):
    hi=max(a,b);return hi+mp.log1p(mp.exp(min(a,b)-hi))


def reject(run,name,fn,kind):
    d=run/'rejected-variants'/name;d.mkdir(parents=True)
    try:fn()
    except AssertionError:
        (d/'stderr.txt').write_text(traceback.format_exc())
        return {'name':name,'status':'ACTUAL_EXPECTED_ASSERTION_ERROR','kind':kind}
    raise RuntimeError('Unrejected false variant: '+name)


def equal(a,b):assert a==b, 'false equality rejected'
def le(a,b):assert a<=b, 'false bound rejected'


def main(run):
    assert sha(S/'PAPER.md')=='75f5d9226c447c8acb4c6e609ac805e57a399a2a0dbfbaf8a3047bd5c22748e9'
    cap=json.loads((R/'INITIAL_CAPTURE.json').read_text())
    for row in cap['files']:assert sha(S/row['path'])==row['sha256']
    m,k,t,a,theta,Q,D=sy.symbols('m k t a theta Q D',positive=True)
    eta=2*(m-2)*k*k/(2-(m-3)*k)
    symbolic=[]
    checks=[sy.diff(eta,k)-2*(m-2)*k*(4-(m-3)*k)/(2-(m-3)*k)**2,
            eta.subs(k,2/(m-1))-2*(m-2)/(m-1)]
    B=Q-1;stationary=1/(t*(a-1))-a/((a-1)*B)
    derivative=B/(1+theta*B)-a*t/(1+t*theta)
    checks.append(derivative.subs(theta,stationary))
    checks.append(sy.diff(derivative,theta)+B*B/(1+theta*B)**2-a*t*t/(1+t*theta)**2)
    W=sy.symbols('W',positive=True)
    numerator=1+theta*((1+k)*W-1)
    checks.append(a*theta*W/numerator-a*theta/(1+k*theta)-a*theta*(1-theta)*(W-1)/(numerator*(1+k*theta)))
    checks.append((3*D/(D+2))/D*(1+(D-1)/3)-1)
    checks.append(2*(D-1)-(D+2)-(D-4))
    for i,expr in enumerate(checks):
        assert sy.factor(expr)==0
        symbolic.append(i+1)
    states=[]
    for m,n in [(2,2),(2,3),(2,10),(3,3),(3,9),(4,4),(4,20),(7,7)]:
        for name,rows in families(m,n):states.append((m,n,name,rows))
    # Exact compact qubit family boundary algebra, with all multiplicities.
    qubit=[]
    for D0 in [6,20,200]:
        for x in [F(0),F(1,8),F(1,4)]:
            raw=[(F(1),D0-2),(1-2*x,1),(x*x,1)]
            qubit.append((2,D0//2,'qubit-A-'+str(x),normalized(D0,raw)))
        for j in sorted({1,2,D0-3}):
            for x in [F(0),F(1,2),F(1)]:
                raw=[(1+2*x,j),(F(1),D0-j-1),(x*x,1)]
                qubit.append((2,D0//2,'qubit-B-'+str(j)+'-'+str(x),normalized(D0,raw)))
            for x in [F(1),F(3,2),F(9,4)]:
                raw=[(1+2*x,j),(x*x,D0-j-2),(F(1),2)]
                qubit.append((2,D0//2,'qubit-C-'+str(j)+'-'+str(x),normalized(D0,raw)))
    for _,n,_,rows in qubit:
        vals=[]
        for y,count in rows:vals.extend([y]*count)
        assert (vals[0]-vals[-2])**2==4*vals[-3]*vals[-1]
    states+=qubit
    exact_rows=[];cache={}
    for m,n,name,rows in states:
        for p in [2,5,m*n+7]:
            z=exact(m,n,p,rows);cache[(m,n,name,p)]=z
            exact_rows.append({'m':m,'D':m*n,'alpha':p,'name':name,
                               'nonzero_chord':bool(z['lam'] and z['width']),
                               'constant_body_nonzero_kernel':bool(not z['width'] and z['hb'])})
    real=[]
    for m,n,name,rows in states[::4]:
        for p in [mp.mpf('2.25'),mp.mpf('64.5'),mp.mpf(m*n)**2+mp.mpf('64.75')]:
            real.append(dict(real_case(m,n,p,rows),name=name))
    scalar=[];lattice=[];high=[]
    for m in [3,4,7,19]:
        q=mp.mpf(m+1)/(m-1);t=q-1;delta=t/2
        u0=(3+q)/2;A=3/mp.log(u0/q)+3/mp.log(3)
        for n in [100,10000]:
            D0=m*n;u=mp.mpf(3)*D0/(D0+2)
            assert u>=u0
            orders=[mp.mpf('2.5'),mp.log(D0),A*mp.log(D0)/2,A*mp.log(D0),(A+1)*mp.log(D0),mp.mpf(D0)**2]
            for p in orders:
                f,th=continuous(q,p);lr=p*mp.log(u)-mp.log(D0)
                assert f>=p*mp.log(q)-mp.log(p)-t-mp.mpf('1e-100')
                etad=2*(m-2)*delta*delta/(2-(m-3)*delta)
                eps=max(mp.exp(p*mp.log1p(delta)-f),mp.power(1-etad/3,p))
                for i in range(13):
                    kap=t*i/12
                    if not kap:values=[mp.log1p(mp.exp(lr))]
                    else:
                        etak=2*(m-2)*kap*kap/(2-(m-3)*kap)
                        head=lr+p*mp.log1p(-etak/3)
                        A0=1+mp.exp(head);B0=mp.expm1(p*mp.log1p(kap))
                        stationary=(B0-p*kap*A0)/(kap*B0*(p-1))
                        candidates=[mp.mpf(0),mp.mpf(1),mp.mpf('0.5'),max(mp.mpf(0),min(mp.mpf(1),stationary))]
                        values=[logsum(mp.log1p(z*B0),head)-p*mp.log1p(kap*z) for z in candidates]
                    for value in values:
                        assert value-max(f,lr)<=mp.log1p(eps)+mp.mpf('1e-90')
                scalar.append({'m':m,'D':D0,'alpha':mp.nstr(p,18),'width_samples':13,'not_global_numerical_optimization':True})
                if p<=A*mp.log(D0):
                    rank=int(mp.floor(D0*th+mp.mpf('.5')))
                    assert 1<=rank<D0 and mp.mpf(rank)/D0>=th/2
                    neighbor=max(logmoment(q,p,mp.mpf(j)/D0) for j in {int(mp.floor(D0*th)),int(mp.ceil(D0*th))} if 1<=j<D0)
                    nearest=logmoment(q,p,mp.mpf(rank)/D0)
                    bound=(4/th**2+p*t*t)/(8*D0**2)
                    loss=f-nearest
                    assert -mp.mpf('1e-100')<=loss<=bound+mp.mpf('1e-100')
                    assert neighbor>=nearest-mp.mpf('1e-100')
                    lattice.append({'m':m,'D':D0,'alpha':mp.nstr(p,18),'rank':rank,'log_loss':mp.nstr(loss,16),'hessian_upper':mp.nstr(bound,16)})
                else:
                    hole=(p-1)*mp.log(mp.mpf(D0)/(D0-1))
                    assert f-lr<=-mp.log(D0) and hole-lr<=-mp.log(D0)
                    tailratio=mp.exp(mp.log(D0-1)-p*mp.log(3))
                    assert tailratio<=1/D0
                    high.append({'m':m,'D':D0,'alpha':mp.nstr(p,18),'integer_candidates_not_unknown_exact_Mstar':True})
    wrong=[]
    z=cache[(2,10,'pole',27)]
    wrong.append(reject(run,'double-count-qubit-peak',lambda:le(z['K']+z['hp']/20,z['M']),
                        'Actual APPT pole at D20; wrong R1 body double counts its dominant peak.'))
    D0=2000;top=F(3*D0,D0+4);cap=F(3*D0,D0+2)
    wrong.append(reject(run,'force-qubit-second-peak-gap',lambda:le(top,F(15,16)*cap),
                        'Actual rank-two projection I+2P has y2/u_D=(D+2)/(D+4)->1.'))
    z=cache[(2,2,'pole',11)]
    wrong.append(reject(run,'erase-qubit-constant-body-mean',lambda:equal(z['hb'],F(0)),
                        'Correct D4 body is one actual positive eigenvalue with nonzero centered kernel.'))
    z=cache[(4,20,'three-level',87)]
    wrong.append(reject(run,'replace-body-by-endpoint-chord',lambda:equal(z['lam'],F(0)),
                        'Actual three-level APPT body has strictly positive power chord loss.'))
    # Exact positive pole perturbation: log loss is small relative to order,
    # while the sharp relative peak moment is exponentially suppressed.
    p=mp.mpf(10000);D0=3*10000**3;coeff=2-1/mp.sqrt(p)
    top=mp.mpf(D0)*(1+coeff)/(D0+coeff);u=mp.mpf(3)*D0/(D0+2)
    h=p*mp.log(u/top);chi=p*mp.log(u)-mp.log(D0)
    assert h/chi<mp.mpf('.004') and mp.exp(-h)<mp.mpf('1e-14')
    wrong.append(reject(run,'relative-log-implies-sharp-moment',lambda:le(h,mp.mpf('.01')),
                        'Actual all-unitary APPT positive pole perturbation; not a finite Mstar calculation.'))
    wrong.append(reject(run,'uncalibrated-three-at-large-order',lambda:le(mp.mpf(400)*mp.log1p(mp.mpf(2)/20),mp.log(2)),
                        'Exact D20 pole base changed from u_D to three at alpha400.'))
    wrong.append(reject(run,'continuous-rank-equals-integer-value',lambda:equal(lattice[1]['log_loss'],'0.0'),
                        'The actual nearest-integer log loss is small but not exactly zero; lattice approximation remains a proved estimate.'))
    return {'status':'PASS','symbolic_controls':symbolic,'exact_spectrum_controls':exact_rows,
            'qubit_family_boundary_checks':len(qubit),'real_order_controls':real,
            'fixed_m_scalar_split_controls':scalar,'integer_lattice_controls':lattice,
            'peak_band_controls':high,'rejected_variants':wrong,'author_code_executed':False,
            'limitations':'Finite diagnostics do not certify all APPT states, non-effective universal rho/Q0, unknown exact finite optima, or global continuous-width extrema. Quibit family membership/classification retains the explicitly credited ordinary external theorem input.'}


if __name__=='__main__':
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    run=R/'reviewer-runs'/stamp;run.mkdir(parents=True)
    (run/'CHECKER_SOURCE.py').write_bytes(Path(__file__).read_bytes())
    record={'status':'RUNNING','utc_started':datetime.now(timezone.utc).isoformat(),
            'script_sha256':sha(Path(__file__)),'runtime':{'python':platform.python_version(),'sympy':sy.__version__,'mpmath':mp.__version__,'mp_dps':mp.mp.dps}}
    try:
        with (run/'stdout.txt').open('w') as out,(run/'stderr.txt').open('w') as err,contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
            result=main(run)
            print(json.dumps({k:len(result[k]) for k in ['symbolic_controls','exact_spectrum_controls','real_order_controls','fixed_m_scalar_split_controls','integer_lattice_controls','peak_band_controls','rejected_variants']}))
        record.update(result)
    except BaseException as e:
        record.update(status='FAIL',exception_type=type(e).__name__,exception=str(e),traceback=traceback.format_exc())
        (run/'unexpected-failure.txt').write_text(traceback.format_exc())
    record['utc_completed']=datetime.now(timezone.utc).isoformat()
    (run/'RESULT.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'run':str(run),'script_sha256':record['script_sha256'],
                      'exception':record.get('exception'),'traceback':record.get('traceback')},ensure_ascii=False))
    sys.exit(0 if record['status']=='PASS' else 1)
