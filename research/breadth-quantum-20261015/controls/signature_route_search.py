"""Test a stronger Hermitian inertia<= (2,2) route, not physical rank2."""
from pathlib import Path
import os,ast
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,scipy.linalg as la
from scipy.optimize import minimize
import json,datetime,time,math
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
Q=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
t=ast.parse((Q/'finite_rank2_search.py').read_text());exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))],type_ignores=[]),'lib','exec'))

def obj(x,k):
    n=3**k;A,B=unpack(x,n);H=A@A.conj().T-B@B.conj().T;norm=np.vdot(H,H).real
    if norm<1e-100:return 1e50,np.zeros_like(x)
    LH=local_form(H,(3,)*k,.5);v=np.vdot(H,LH).real/norm;M=(LH-v*H)/norm
    return float(v),pack(4*M@A,-4*M@B)

rng=np.random.default_rng(1535);records=[];controls=[]
for k in [2,3]:
    n=3**k;A=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2));B=rng.normal(size=(n,2))+1j*rng.normal(size=(n,2));x=pack(A,B);h=rng.normal(size=x.shape);h/=la.norm(h);v,g=obj(x,k);eps=2e-5;fd=(obj(x+eps*h,k)[0]-obj(x-eps*h,k)[0])/(2*eps);an=float(g@h);assert abs(fd-an)<1e-6;controls.append({'k':k,'gradient_error':abs(fd-an)})
    for trial in range(80):
        A=la.qr(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)),mode='economic')[0];B=la.qr(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)),mode='economic')[0]
        res=minimize(lambda z:obj(z,k),pack(A,B),jac=True,method='L-BFGS-B',options={'maxiter':1000,'ftol':2e-14,'gtol':1e-9})
        A,B=unpack(res.x,n);H=A@A.conj().T-B@B.conj().T;ev=la.eigvalsh(H)
        rec={'k':k,'trial':trial,'value':float(res.fun),'inertia_positive':int(np.sum(ev>1e-7)),'inertia_negative':int(np.sum(ev<-1e-7)),'rank':int(np.sum(abs(ev)>1e-7)),'interpretation':'This is the stronger signature cone, not a rank-two NPT witness.'};records.append(rec)
        if res.fun<-1e-7:
            np.savez_compressed(Q/f'signature-route-negative-k{k}.npz',A=A,B=B,H=H);print(json.dumps(rec),flush=True);break
(P/'SIGNATURE_ROUTE_SEARCH.json').write_text(json.dumps({'schema':'strong-Hermitian-signature-route-probe-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'A sufficient Hermitian inertia2,2 extension would cover real/imaginary parts of actual rank2 matrices. Negative rank3/4 here refutes only that stronger extension.','gradient_controls':controls,'records':records,'complete_target_solved':False},indent=2)+'\n')
print(json.dumps({'kinds':len(records),'min':min(r['value'] for r in records)}),flush=True)
