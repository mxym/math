"""Finite product-vector probes of a self-partial-transpose Choi family.
Known orthogonally covariant single-site map family; no new TSP construction.
No claim that an indefinite Choi operator is a physical density matrix.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,scipy.linalg as la
from scipy.optimize import minimize
import json,argparse,time,datetime
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=480);args=ap.parse_args()
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
target=P/'ORTHOGONAL_MAP_PROBE.json';assert not target.exists()
def channel(C,k,d,eps):
    a=C.reshape((d,)*(2*k));eye=np.eye(d)
    for i in range(k):
        x=np.moveaxis(a,(i,k+i),(0,1));tr=np.trace(x,axis1=0,axis2=1)
        b=(1-eps)*eye.reshape((d,d)+(1,)*(2*k-2))*tr-(x+x.swapaxes(0,1))/(d+1)
        a=np.moveaxis(b,(0,1),(i,k+i))
    return a.reshape(d**k,d**k)
def obj(x,k,d,eps):
    n=d**k;z=x.reshape(4,n);u=z[0]+1j*z[1];v=z[2]+1j*z[3];nu=np.vdot(u,u).real;nv=np.vdot(v,v).real
    if nu*nv<1e-100:return 1e40,np.zeros_like(x)
    Mu=channel(np.outer(u,u.conj()),k,d,eps);Mv=channel(np.outer(v,v.conj()),k,d,eps)
    raw=np.vdot(u,Mv@u).real;q=raw/(nu*nv)
    gu=2*(Mv@u/(nu*nv)-q*u/nu);gv=2*(Mu@v/(nu*nv)-q*v/nv)
    return q,np.stack([gu.real,gu.imag,gv.real,gv.imag]).ravel()
rng=np.random.default_rng(202610150810);controls=[]
for k,d,eps in [(2,2,.25),(2,3,.1),(3,3,.2)]:
    x=rng.normal(size=4*d**k);v=rng.normal(size=x.size);v/=la.norm(v);h=1e-5
    err=abs((obj(x+h*v,k,d,eps)[0]-obj(x-h*v,k,d,eps)[0])/(2*h)-obj(x,k,d,eps)[1]@v)
    assert err<1e-7;controls.append({'k':k,'d':d,'epsilon':eps,'gradient_error':err})
a=np.array([1,1j])/np.sqrt(2);b=a.conj();u=(np.kron(a,a)+np.kron(b,b))/np.sqrt(2)
M=channel(np.outer(u,u.conj()),2,2,.25);neg=float(la.eigvalsh(M)[0]);assert neg<-.001
controls.append({'d2_valid_positive_single_site_epsilon':.25,'k2_negative_eigenvalue':neg,'why_admissible':'The single-site Choi is block positive for epsilon<=1/3, and the tensor output is explicitly indefinite.'})
records=[];best={};start=time.monotonic();trial=0
out={'schema':'finite-self-transpose-orthogonal-map-probe-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Finite product-vector tests for J=(1-epsilon)I-(F+Omega_un)/(d+1). This is an attributed orthogonally covariant map family. Indefinite Choi operators are not density matrices. Neither all-copy positivity nor physical N0 is proved.','controls':controls,'records':records,'best':best,'complete_target_solved':False}
while time.monotonic()-start<args.seconds:
    k=[2,3,4,5][trial%4];eps=[.05,.1,.2,.24][(trial//4)%4];trial+=1;n=3**k;x=rng.normal(size=4*n)
    res=minimize(lambda x:obj(x,k,3,eps),x,jac=True,method='L-BFGS-B',options={'maxiter':100,'ftol':1e-12,'gtol':1e-8})
    val=float(res.fun);key=f'd3-k{k}-eps{eps}'
    rec={'trial':trial,'k':k,'d':3,'epsilon':eps,'product_expectation':val,'iterations':int(res.nit),'success':bool(res.success),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};records.append(rec)
    if key not in best or val<best[key]['product_expectation']:
        best[key]=rec
        if val<-1e-8:
            np.savez(P/f'orthogonal-negative-{key}.npz',x=res.x);out['negative_route_candidate']=rec
    if trial%4==0:
        out['elapsed_seconds']=time.monotonic()-start;target.write_text(json.dumps(out,indent=2)+'\n')
out['elapsed_seconds']=time.monotonic()-start;out['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'trajectories':trial,'seconds':out['elapsed_seconds'],'best':best,'complete_target_solved':False}))
