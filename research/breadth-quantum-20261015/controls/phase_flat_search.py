"""Continuous non-Clifford complex flat-phase crossed-Gram probes.
Orthogonality is exact by a nonzero Pauli character, independent of phase.
No finite search is used as an arbitrary-copy or global proof.
"""
from pathlib import Path
import os,ast
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
for filename in ['finite_rank2_search.py','graph_code_exact.py','crossed_gram_search.py']:
    module=ast.parse((PRIVATE/filename).read_text());pure=ast.Module(body=[n for n in module.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))],type_ignores=[]);exec(compile(pure,filename,'exec'),globals())
from scipy.optimize import minimize
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=1600);args=ap.parse_args()

def phase_objective(x,k,ub,vc):
    n=3**k;u=np.exp(1j*x[:n])/math.sqrt(n);v=np.exp(1j*x[n:])/math.sqrt(n)
    U=np.stack([u,ub*u],axis=1);V=np.stack([v,vc*v],axis=1)
    value,(GU,GV),meta=objective(U,V,k,0.)
    gu=np.imag(U.conj()*GU).sum(axis=1);gv=np.imag(V.conj()*GV).sum(axis=1)
    return -value,-np.r_[gu,gv]

rng=np.random.default_rng(151530)
controls=[]
for k in [2,3]:
    n=3**k;X=ternary_vectors(k);b=np.r_[1,np.zeros(k-1,int)];c=np.ones(k,int)
    ub=np.exp(2j*np.pi*((X@b)%3)/3);vc=np.exp(2j*np.pi*((X@c)%3)/3)
    x=rng.uniform(-np.pi,np.pi,size=2*n);h=rng.normal(size=2*n);h/=la.norm(h)
    val,gr=phase_objective(x,k,ub,vc);eps=1e-5
    fd=(phase_objective(x+eps*h,k,ub,vc)[0]-phase_objective(x-eps*h,k,ub,vc)[0])/(2*eps);an=float(gr@h)
    assert abs(fd-an)<1e-6
    controls.append({'k':k,'gradient_error':abs(fd-an)})
print(json.dumps({'event':'phase_gradient_controls_passed','checks':controls}),flush=True)
start=time.monotonic();stop=start+args.seconds
summary={'schema':'finite-continuous-phase-gram-probes-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Finite nonnormal flat-phase orthogonal two-planes; phase parameters continuous and complex, not restricted to Clifford roots. Not full-domain or arbitrary-copy proof.','controls':controls,'records':[],'best':{}}
trial=0
while time.monotonic()<stop:
    k=[3,4,5,3,4][trial%5];n=3**k;X=ternary_vectors(k)
    b=rng.integers(0,3,size=k);c=rng.integers(0,3,size=k)
    if not np.any(b):b[0]=1
    if not np.any(c):c[-1]=1
    ub=np.exp(2j*np.pi*((X@b)%3)/3);vc=np.exp(2j*np.pi*((X@c)%3)/3)
    assert abs(ub.sum())<1e-10 and abs(vc.sum())<1e-10
    x=rng.uniform(-np.pi,np.pi,size=2*n)
    if trial%3==1:
        # Perturb stabilizer/quadratic phases, then optimize arbitrary
        # individual phases, so no Clifford restriction survives.
        for offset in [0,n]:
            G=np.triu(rng.normal(size=(k,k)),1)
            x[offset:offset+n]=np.sum((X@G)*X,axis=1)+rng.normal(size=n)*.1
    before=time.monotonic()
    def callback(v):
        if time.monotonic()>stop:raise StopIteration()
    res=minimize(lambda v:phase_objective(v,k,ub,vc),x,jac=True,method='L-BFGS-B',callback=callback,options={'maxiter':2000,'ftol':2e-14,'gtol':1e-9,'maxls':40,'maxcor':30})
    val=float(res.fun);u=np.exp(1j*res.x[:n])/math.sqrt(n);v=np.exp(1j*res.x[n:])/math.sqrt(n)
    U=np.stack([u,ub*u],axis=1);V=np.stack([v,vc*v],axis=1)
    _,_,meta=objective(U,V,k,0.);bu,gu,miu=local_barrier(U,k);bv,gv,miv=local_barrier(V,k)
    rec={'trial':trial,'k':k,'b':b.tolist(),'c':c.tolist(),'log_ratio_squared':-val,'iterations':int(res.nit),'success':bool(res.success),'message':str(res.message),'min_local_support_eigenvalue':min(miu+miv),'seconds':time.monotonic()-before,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    summary['records'].append(rec);key=str(k)
    if -val>summary['best'].get(key,{'log_ratio_squared':-1e100})['log_ratio_squared']:
        summary['best'][key]=rec;np.savez_compressed(PRIVATE/f'phase-flat-best-k{k}.npz',U=U,V=V,b=b,c=c,x=res.x)
    summary['elapsed_seconds']=time.monotonic()-start
    (PUBLIC/'PHASE_FLAT_SEARCH.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    if -val>1e-7:summary['negative_candidate_requires_exact_rank2_reconstruction']=True;break
    trial+=1
summary['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();summary['complete_target_solved']=False
(PUBLIC/'PHASE_FLAT_SEARCH.json').write_text(json.dumps(summary,indent=2)+'\n')
