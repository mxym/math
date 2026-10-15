"""Strong four-ray tensor-contraction certificate test; not the N0 target."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la, itertools,json,datetime
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
Q=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
def swap(d,i,j):
    n=d**4;base=np.arange(n).reshape((d,)*4);p=list(range(4));p[i],p[j]=p[j],p[i]
    out=np.zeros((n,n));out[np.arange(n),base.transpose(p).ravel()]=1;return out
records=[]
for d in [2,3,4]:
    n=d**4;I=np.eye(n);R13=I-.5*swap(d,0,2);R24=I-.5*swap(d,1,3)
    A=R13@R24;B=swap(d,2,3)@A@swap(d,0,1);assert la.norm(B-B.T)<1e-12
    eig,ve=la.eigh(A,driver='evd');Ai=(ve/np.sqrt(eig))@ve.T;C=Ai@B@Ai
    ev,vec=la.eigh(C,driver='evd');rec={'d':d,'min_generalized_eigenvalue':float(ev[0]),'max_generalized_eigenvalue':float(ev[-1]),'contraction_holds_numerically':bool(ev[0]>-1-1e-10 and ev[-1]<1+1e-10)}
    records.append(rec);print(json.dumps(rec),flush=True)
    if ev[-1]>1+1e-8 or ev[0]<-1-1e-8:np.savez_compressed(Q/f'four-ray-failed-d{d}.npz',A=A,B=B,contracted=C,values=ev,vectors=vec)
(P/'FOUR_RAY_CERTIFICATE.json').write_text(json.dumps({'schema':'strong-four-ray-tensor-route-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'A uniform local Loewner contraction would tensorize the four-ray determinant. Failure only rejects this stronger sufficient route; it is not an actual rank-two physical witness.','records':records,'complete_target_solved':False},indent=2)+'\n')
