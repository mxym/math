"""Finite four-copy qutrit-memory filter search with exact rank2 pullback.
The final sparse two-copy witness is from Tabia–Chen–Hsieh2608.08836v2.
Only local prefilters are varied; no full-domain inference is made.
"""
from pathlib import Path
import os,ast
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np,scipy.linalg as la
from scipy.optimize import minimize
import argparse,json,datetime,time,math
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
Q=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
tree=ast.parse((Q/'finite_rank2_search.py').read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))],type_ignores=[]),'lib','exec'))
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=600);args=ap.parse_args()
C0=np.zeros((9,9),complex)
for r in [1,2]:
    u=np.zeros(9);v=np.zeros(9);u[r]=u[3*r]=1/math.sqrt(2);v[r]=1/math.sqrt(2);v[3*r]=-1/math.sqrt(2)
    C0+=np.outer(u,v)/math.sqrt(2)
assert np.linalg.matrix_rank(C0)==2 and abs(np.vdot(C0,C0)-1)<1e-12
def ppack(A,B):return np.stack([A.real,A.imag,B.real,B.imag]).ravel()
def punpack(x):
    x=x.reshape(4,3,9);return x[0]+1j*x[1],x[2]+1j*x[3]
def obj(x,lam=.5):
    A,B=punpack(x);FA=np.kron(A,A);FB=np.kron(B,B);D=FA.conj().T@C0@FB;norm=np.vdot(D,D).real
    if norm<1e-200:return 1e50,np.zeros_like(x)
    LD=local_form(D,(3,)*4,lam);val=float(np.vdot(D,LD).real/norm);G=2*(LD-val*D)/norm
    GFA=C0@FB@G.conj().T;GFB=C0.conj().T@FA@G
    def chain(T,M):
        T=T.reshape(3,3,9,9);return np.einsum('ikjl,kl->ij',T,M.conj())+np.einsum('ikjl,ij->kl',T,M.conj())
    return val,ppack(chain(GFA,A),chain(GFB,B))

rng=np.random.default_rng(153160);controls=[]
for lam in [.4,.5,.75]:
    A=rng.normal(size=(3,9))+1j*rng.normal(size=(3,9));B=rng.normal(size=(3,9))+1j*rng.normal(size=(3,9));x=ppack(A,B);h=rng.normal(size=x.shape);h/=la.norm(h);val,g=obj(x,lam);eps=1e-5;fd=(obj(x+eps*h,lam)[0]-obj(x-eps*h,lam)[0])/(2*eps);an=float(g@h);assert abs(fd-an)<1e-6;controls.append({'lambda':lam,'gradient_error':abs(fd-an)})
A=np.zeros((3,9),complex)
for i in range(3):A[i,3*i]=1
value=obj(ppack(A,A),.75)[0];assert value<0
controls.append({'known_rank2_negative_lambda':.75,'value':value,'expected_normalized':1-1.5*.75})
assert abs(value-(1-1.5*.75))<1e-12
start=time.monotonic();stop=start+args.seconds
summary={'schema':'finite-four-copy-memory3-variational-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Actual complex product prefilters on two input-copy blocks, followed by an attributed rank-two canonical witness on two outputs; a four-copy restricted protocol. No general or all-copy proof.','source':'https://arxiv.org/html/2608.08836v2','controls':controls,'records':[],'best':{}}
print(json.dumps({'event':'memory3_gradient_controls_passed','checks':controls}),flush=True)
trial=0
while time.monotonic()<stop:
    lam=[.5,.49,.4,.5][trial%4]
    A=la.qr(rng.normal(size=(9,3))+1j*rng.normal(size=(9,3)),mode='economic')[0].conj().T
    B=la.qr(rng.normal(size=(9,3))+1j*rng.normal(size=(9,3)),mode='economic')[0].conj().T
    before=time.monotonic()
    def callback(x):
        if time.monotonic()>stop:raise StopIteration()
    res=minimize(lambda x:obj(x,lam),ppack(A,B),jac=True,method='L-BFGS-B',callback=callback,options={'maxiter':1500,'ftol':2e-14,'gtol':1e-9,'maxls':40,'maxcor':25})
    A,B=punpack(res.x);FA=np.kron(A,A);FB=np.kron(B,B);D=FA.conj().T@C0@FB;ev=la.svdvals(D)
    rec={'trial':trial,'lambda':lam,'Q_over_HS2':float(res.fun),'iterations':int(res.nit),'success':bool(res.success),'message':str(res.message),'image_singular_values_first4':ev[:4].tolist(),'seconds':time.monotonic()-before,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};summary['records'].append(rec);key=str(lam)
    if res.fun<summary['best'].get(key,{'Q_over_HS2':1e100})['Q_over_HS2']:
        summary['best'][key]=rec;np.savez_compressed(Q/f'memory3-best-lambda-{lam}.npz',A=A,B=B,C=D)
    summary['elapsed_seconds']=time.monotonic()-start
    (P/'MEMORY3_VARIATIONAL.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(rec),flush=True)
    if res.fun<-1e-7:summary['negative_candidate_requires_exact_reconstruction']=True;break
    trial+=1
summary['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();summary['complete_target_solved']=False
(P/'MEMORY3_VARIATIONAL.json').write_text(json.dumps(summary,indent=2)+'\n')
