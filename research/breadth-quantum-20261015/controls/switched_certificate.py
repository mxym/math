"""Test a proposed stronger co-Choi certificate; failure is not N0 failure."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la, itertools,json,datetime
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')

def Rmatrix(d,k):
    n=d**k;R=np.eye(n*n)
    base=np.arange(n*n).reshape((d,)*(2*k))
    for m in range(1,1<<k):
        perm=list(range(2*k));count=0
        for i in range(k):
            if m>>i&1:perm[i],perm[k+i]=perm[k+i],perm[i];count+=1
        loc=base.transpose(perm).reshape(-1)
        R[np.arange(n*n),loc]+=(-.5)**count
    return R

def certificate(R,u):
    n=len(u);blocks=R.reshape(n,n,n,n)
    A=np.einsum('a,acbd,b->cd',u.conj(),blocks,u)
    Ai=la.inv(A)
    L=np.einsum('a,acbd->bcd',u.conj(),blocks)
    M=np.empty_like(R,dtype=complex)
    for a in range(n):
        for b in range(n):M[b*n:(b+1)*n,a*n:(a+1)*n]=L[a]@Ai@L[b].conj().T
    C=R-M;assert la.norm(C-C.conj().T)<1e-10
    return C,A,L

records=[];rng=np.random.default_rng(151518)
for k in [1,2,3]:
    d=3;n=d**k;R=Rmatrix(d,k)
    for case in ['product','maxentangled' if k==2 else 'random']:
        if case=='product':u=np.eye(1,n,0).ravel().astype(complex)
        elif case=='maxentangled':u=np.eye(3).ravel()/np.sqrt(3)
        else:u=rng.normal(size=n)+1j*rng.normal(size=n);u/=la.norm(u)
        C,A,L=certificate(R,u)
        ev,ve=la.eigh(C,driver='evd');assert la.norm(ve.T.conj()@ve-np.eye(n*n))<1e-9
        rec={'k':k,'case':case,'certificate_dimension':n*n,'min_eigenvalue':float(ev[0]),'max_eigenvector_residual':float(la.norm(C@ve[:,0]-ev[0]*ve[:,0])),'negative_count_tol_1e-9':int(np.sum(ev<-1e-9)),'interpretation':'Negative here rejects only co-Choi-PSD sufficient certificate, not the switched inequality on positive inputs or rank-two Werner nonnegativity.'}
        records.append(rec)
        if ev[0]<-1e-8:np.savez_compressed(PRIVATE/f'switched-negative-k{k}-{case}.npz',u=u,R=R,C=C,witness=ve[:,0])
        print(json.dumps(rec),flush=True)
(PUBLIC/'SWITCHED_CERTIFICATE.json').write_text(json.dumps({'schema':'strong-co-Choi-route-control-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':records,'complete_target_solved':False},indent=2)+'\n')
