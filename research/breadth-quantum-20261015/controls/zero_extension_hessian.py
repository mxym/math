"""Unrestricted rank-two manifold Hessian at qubit-supported endpoint zeros.
Matrix-free Hessian: no normality restriction on perturbations.
Finite-copy diagnostics only, not a proof for any arbitrary copy count.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la, scipy.sparse.linalg as sla
import json,datetime,time,math
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
exec((PRIVATE/'null_quartic.py').read_text().split('rng=np.random.default_rng(1533)')[0])

def frames(k,rng):
    pair=la.qr(rng.normal(size=(2**k,2))+1j*rng.normal(size=(2**k,2)),mode='economic')[0]
    u,v=pair.T
    w1=(-1)**k*antistate(v,k);w2=-(-1)**k*antistate(u,k)
    U=np.stack([embed(u,k),embed(v,k)],axis=1)
    W=np.stack([embed(w1,k),embed(w2,k)],axis=1)
    return U,W

def operator(U,W,k):
    n=len(U);V=la.null_space(U.conj().T);Z=la.null_space(W.conj().T)
    C0=U@W.conj().T;L0=local_form(C0,(3,)*k,.5)
    K=V.conj().T@L0@Z
    size=8*n-8
    calls=[0]
    def mv(z):
        calls[0]+=1
        S,X,Y=unpack_chart(z,n)
        D=U@S@W.conj().T+(V@X)@W.conj().T+U@(Z@Y).conj().T
        LD=local_form(D,(3,)*k,.5)
        a=U.conj().T@LD@W
        b=V.conj().T@LD@W+K@Y
        c=Z.conj().T@LD.conj().T@U+K.conj().T@X
        return pack_chart(a,b,c)
    H=sla.LinearOperator((size,size),matvec=mv,rmatvec=mv,dtype=float)
    return H,C0,V,Z,calls

rng=np.random.default_rng(151515)
records=[]
for k in [3,4,5,6]:
    for trial in range(2):
        start=time.monotonic();U,W=frames(k,rng)
        H,C0,V,Z,calls=operator(U,W,k)
        z=rng.normal(size=H.shape[0]);z/=la.norm(z)
        w=rng.normal(size=H.shape[0]);w/=la.norm(w)
        symerr=abs(np.dot(w,H@z)-np.dot(z,H@w));assert symerr<1e-11
        S,X,Y=unpack_chart(z,len(U))
        pred=np.dot(z,H@z);checks=[]
        for eps in [.002,.001]:
            Cp=(U+eps*V@X)@(np.eye(2)+eps*S)@(W+eps*Z@Y).conj().T
            Cm=(U-eps*V@X)@(np.eye(2)-eps*S)@(W-eps*Z@Y).conj().T
            val=(q(Cp,k)+q(Cm,k)-2*q(C0,k))/(2*eps**2)
            checks.append({'eps':eps,'measured':val,'predicted':float(pred),'error':float(abs(val-pred))})
        assert checks[-1]['error']<1e-5
        # Multiple smallest algebraic Ritz values, with actual residuals.
        # A zero Ritz value is not treated as a positive global margin.
        ev,ve=sla.eigsh(H,k=12,which='SA',tol=1e-10,maxiter=5000,ncv=48)
        residuals=[la.norm(H@ve[:,j]-ev[j]*ve[:,j]) for j in range(len(ev))]
        ortherr=la.norm(ve.T@ve-np.eye(len(ev)));assert ortherr<1e-9
        assert max(residuals)<1e-7
        rec={'k':k,'trial':trial,'variables':H.shape[0],'q0':q(C0,k),'symmetry_error':float(symerr),'chart_checks':checks,'smallest_ritz_values':ev.tolist(),'max_ritz_residual':float(max(residuals)),'ritz_orthogonality_error':float(ortherr),'matvec_calls':calls[0],'seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
        records.append(rec)
        np.savez_compressed(PRIVATE/f'zero-extension-k{k}-trial{trial}.npz',U=U,W=W,ritz_values=ev,ritz_vectors=ve)
        (PUBLIC/'ZERO_EXTENSION_HESSIAN.json').write_text(json.dumps({'schema':'qubit-zero-extension-finite-hessian-v1','scope':'Finite-copy tangent diagnostics; negative Ritz candidates require exact reconstruction; nonnegative diagnostics do not prove full-domain positivity','records':records},indent=2)+'\n')
        print(json.dumps(rec),flush=True)
