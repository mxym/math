"""Exploration only: fixed-copy low-rank Rayleigh optimization.

No finite result of this program proves arbitrary-copy undistillability.
The mathematical rank restriction is imposed by C=A B*, not by a penalty.
"""
from pathlib import Path
import argparse, datetime, itertools, json, math, os, signal, time
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import numpy as np
from scipy.optimize import minimize

PARSER=argparse.ArgumentParser()
PARSER.add_argument('--seconds',type=float,default=1200)
PARSER.add_argument('--seed',type=int,default=150615)
PARSER.add_argument('--controls-only',action='store_true')
ARGS=PARSER.parse_args()
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
PRIVATE.mkdir(parents=True,exist_ok=True)
STOP=PRIVATE/'STOP_SEARCH'
started=time.monotonic()
utc=lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
stopping=False
def mark_stop(signum,frame):
    global stopping
    stopping=True
signal.signal(signal.SIGTERM,mark_stop)
signal.signal(signal.SIGINT,mark_stop)

def local_form(C,dims,lam):
    """Product of the commuting maps Id-lambda Tr_i^* Tr_i."""
    count=len(dims)
    total=math.prod(dims)
    Y=C.copy()
    for i,d in enumerate(dims):
        others=[j for j in range(count) if j!=i]
        perm=[i]+others+[count+i]+[count+j for j in others]
        inverse=np.argsort(perm)
        local=Y.reshape(tuple(dims)*2).transpose(perm).reshape(d,total//d,d,total//d).copy()
        contraction=np.einsum('aiaj->ij',local)
        for a in range(d):
            local[a,:,a,:]-=lam*contraction
        Y=local.reshape((d,)+tuple(dims[j] for j in others)+(d,)+tuple(dims[j] for j in others)).transpose(inverse).reshape(total,total)
    return Y

def partial_trace(C,dims,J):
    current=list(dims)
    out=C.reshape(tuple(dims)*2)
    for j in sorted(J,reverse=True):
        out=np.trace(out,axis1=j,axis2=len(current)+j)
        current.pop(j)
    return np.asarray(out).reshape(math.prod(current),math.prod(current))

def subset_form(C,dims,lam):
    return sum((-lam)**len(J)*np.vdot(partial_trace(C,dims,J),partial_trace(C,dims,J)).real for n in range(len(dims)+1) for J in itertools.combinations(range(len(dims)),n))

def unpack(x,n):
    packed=x.reshape(2,2,n,2)
    return packed[0,0]+1j*packed[0,1],packed[1,0]+1j*packed[1,1]

def pack(A,B):
    return np.stack([np.stack([A.real,A.imag]),np.stack([B.real,B.imag])]).ravel()

def value_gradient(x,dims,lam=.5):
    n=math.prod(dims)
    A,B=unpack(x,n)
    C=A@B.conj().T
    norm=np.vdot(C,C).real
    if norm<1e-200:
        return 1e50,np.zeros_like(x)
    L=local_form(C,dims,lam)
    value=np.vdot(C,L).real/norm
    residual=(L-value*C)/norm
    GA=2*residual@B
    GB=2*residual.conj().T@A
    return float(value),pack(GA,GB)

def basis(n,j):
    x=np.zeros(n,dtype=complex); x[j]=1
    return x

def controls():
    rng=np.random.default_rng(ARGS.seed)
    checks=[]
    for dims in [(2,3),(3,3,3),(2,3,2,2)]:
        n=math.prod(dims)
        A=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2))
        B=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2))
        C=A@B.conj().T
        lhs=np.vdot(C,local_form(C,dims,.5)).real
        rhs=subset_form(C,dims,.5)
        err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
        assert err<5e-13,(dims,lhs,rhs)
        x=pack(A,B); h=rng.normal(size=x.shape); h/=np.linalg.norm(h)
        val,gradient=value_gradient(x,dims)
        eps=2e-5
        finite=(value_gradient(x+eps*h,dims)[0]-value_gradient(x-eps*h,dims)[0])/(2*eps)
        analytic=np.dot(gradient,h)
        assert abs(finite-analytic)<1e-7,(dims,finite,analytic)
        checks.append({'dims':dims,'local_vs_subset_relative_error':float(err),'directional_gradient_error':float(abs(finite-analytic))})
    # The endpoint has legal rank-two zeros, and lambda>1/2 has known
    # rank-two negative directions. Padding is by rank-one trace-zero slots.
    for k in (1,2,3,4):
        C=np.diag([1,1,0]).astype(complex)
        for _ in range(k-1):
            C=np.kron(C,np.outer(basis(3,0),basis(3,1)))
        assert abs(subset_form(C,(3,)*k,.5))<1e-12
        value=subset_form(C,(3,)*k,.51)
        assert abs(value+.04)<1e-12
        checks.append({'negative_control_copies':k,'rank':2,'Q_lambda_051':float(value)})
    # A negative rank-three coefficient is inadmissible at lambda=1/2.
    C=np.kron(np.kron(np.array([[0,1],[0,0]],complex),np.array([[0,1],[0,0]],complex)),np.eye(3)/math.sqrt(3))
    value=subset_form(C,(2,2,3),.5)
    assert np.linalg.matrix_rank(C)==3 and abs(value+.5)<1e-12
    checks.append({'inadmissible_rank3_negative_Q':float(value),'rank':3})
    return checks

controls_record={'schema':'finite-copy-search-control-v1','created_utc':utc(),'checks':controls(),'claim':'program controls only; not a global or arbitrary-copy proof'}
(PUBLIC/'SEARCH_CONTROLS.json').write_text(json.dumps(controls_record,indent=2)+'\n')
print(json.dumps({'event':'controls_passed','utc':utc(),'checks':len(controls_record['checks'])}),flush=True)
if ARGS.controls_only:
    raise SystemExit(0)

rng=np.random.default_rng(ARGS.seed)
cases=[(3,3,3),(3,3,3),(3,3,3,3),(3,3,3,3),(3,3,3,3,3)]
summary={'schema':'finite-copy-rank2-search-v1','started_utc':utc(),'seed':ARGS.seed,'runtime_seconds_requested':ARGS.seconds,'scope':'Finite k only; real and imaginary parameters unconstrained; C=A B* has rank<=2; no all-k proof or major result','records':[],'best':{}}
record_path=PUBLIC/'SEARCH_PROGRESS.json'
iteration=0
while not stopping and not STOP.exists() and time.monotonic()-started<ARGS.seconds:
    dims=cases[iteration%len(cases)]
    n=math.prod(dims)
    # Two input/output planes need not agree. Every fifth start is a
    # perturbation of a legal zero to test tangential nonnormal escapes.
    A=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2))
    B=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2))
    if iteration%5==4:
        a=np.zeros((n,2),complex); b=np.zeros((n,2),complex)
        for j in range(2):
            first=j*3**(len(dims)-1)
            last=first+sum(3**s for s in range(len(dims)-1))
            a[first,j]=1;b[last,j]=1
        A=a+.02*A/math.sqrt(n);B=b+.02*B/math.sqrt(n)
    A=np.linalg.qr(A)[0];B=np.linalg.qr(B)[0]
    x=pack(A,B)
    calls=[0]
    def fun(x):
        calls[0]+=1
        return value_gradient(x,dims)
    def callback(x):
        if stopping or STOP.exists() or time.monotonic()-started>=ARGS.seconds:
            raise StopIteration()
    before=time.monotonic()
    res=minimize(fun,x,jac=True,method='L-BFGS-B',callback=callback,options={'maxiter':1800,'ftol':2e-14,'gtol':2e-10,'maxls':40,'maxcor':20})
    value=float(res.fun)
    key='x'.join(map(str,dims))
    item={'start':iteration,'dims':dims,'utc':utc(),'seconds':time.monotonic()-before,'iterations':int(res.nit),'evaluations':calls[0],'Q_over_HS2':value,'optimizer_success':bool(res.success),'optimizer_message':str(res.message)}
    summary['records'].append(item)
    if value<summary['best'].get(key,{'Q_over_HS2':float('inf')})['Q_over_HS2']:
        A,B=unpack(res.x,n)
        np.savez_compressed(PRIVATE/('best-'+key+'.npz'),A=A,B=B)
        summary['best'][key]=item
    summary['last_utc']=utc();summary['elapsed_computation_seconds']=time.monotonic()-started
    record_path.write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(item),flush=True)
    if value<-1e-9:
        summary['negative_candidate_requires_exact_reconstruction']=True
        break
    iteration+=1
summary['closed_utc']=utc();summary['stopped_by_flag']=stopping or STOP.exists();summary['elapsed_computation_seconds']=time.monotonic()-started
summary['complete_target_solved']=False
record_path.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'event':'search_closed','utc':utc(),'best':summary['best'],'starts':len(summary['records'])}),flush=True)
