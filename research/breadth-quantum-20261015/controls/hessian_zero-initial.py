"""Rank-two tangent tests at exact endpoint zeros; finite controls only."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la, datetime, json, math
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
# Only the pure library definitions, deliberately excluding all script I/O.
source=(PRIVATE/'finite_rank2_search.py').read_text().split('controls_record=')[0]
source=source[source.index('def local_form'):source.index('def controls')]
exec(source)

def embed(v,k,d=3):
    w=np.zeros(d**k,complex)
    for j,x in enumerate(v):
        digs=np.unravel_index(j,(2,)*k)
        w[np.ravel_multi_index(digs,(d,)*k)]=x
    return w

def antistate(u,k):
    signs=np.array([(-1)**(k-bin(j).count('1')) for j in range(2**k)])
    return signs*np.conj(u[::-1])

def q(C,k):
    return float(np.vdot(C,local_form(C,(3,)*k,.5)).real)

def hessian(U,k):
    n=len(U)
    V=la.null_space(U.conj().T)
    C0=U@U.conj().T
    L0=local_form(C0,(3,)*k,.5)
    basis=[];meta=[]
    for what,count in [('S',2),('X',n-2),('Y',n-2)]:
        for a in range(count):
            for b in range(2):
                for phase in [1,1j]:
                    if what=='S':
                        D=phase*np.outer(U[:,a],U[:,b].conj())
                    elif what=='X':
                        D=phase*np.outer(V[:,a],U[:,b].conj())
                    else:
                        D=phase.conjugate()*np.outer(U[:,b],V[:,a].conj())
                    basis.append(D);meta.append((what,a,b,phase))
    B=np.stack(basis)
    LB=np.stack([local_form(D,(3,)*k,.5) for D in B])
    H=np.einsum('aij,bij->ab',B.conj(),LB).real
    # q(D)+2 Re <L0,V X Y* V*>. This changes only X,Y blocks.
    K=V.conj().T@L0@V
    for i,(wi,ai,bi,pi) in enumerate(meta):
        if wi!='X':continue
        for j,(wj,aj,bj,pj) in enumerate(meta):
            if wj!='Y' or bi!=bj:continue
            val=(pi*pj.conjugate()*K[ai,aj].conjugate()).real
            H[i,j]+=val;H[j,i]+=val
    eig,vec=la.eigh(H)
    scale=max(1,la.norm(H,2))
    # Direct chart check using a non-eigenvector real tangent.
    rng=np.random.default_rng(15151+k)
    coeff=rng.normal(size=len(meta));coeff/=np.linalg.norm(coeff)
    S=np.zeros((2,2),complex);X=np.zeros((n-2,2),complex);Y=X.copy()
    for c,(w,a,b,p) in zip(coeff,meta):
        {'S':S,'X':X,'Y':Y}[w][a,b]+=c*p
    pred=float(coeff@H@coeff)
    errors=[]
    for eps in [.01,.001,.0001]:
        Cp=(U+eps*V@X)@(np.eye(2)+eps*S)@(U+eps*V@Y).conj().T
        Cm=(U-eps*V@X)@(np.eye(2)-eps*S)@(U-eps*V@Y).conj().T
        measured=(q(Cp,k)+q(Cm,k)-2*q(C0,k))/(2*eps**2)
        errors.append({'epsilon':eps,'measured_quadratic':measured,'predicted':pred,'error':abs(measured-pred)})
    assert errors[1]['error']<1e-5
    return {'k':k,'variables':len(meta),'q0':q(C0,k),'min_eigenvalue':float(eig[0]),'max_eigenvalue':float(eig[-1]),'null_count_tol_1e-9':int(np.sum(abs(eig)<1e-9)),'negative_count_tol_1e-9':int(np.sum(eig<-1e-9)),'chart_checks':errors},eig,vec,meta,V

rng=np.random.default_rng(150615)
records=[]
for k in [3,5]:
    if k==5:break
    for trial in range(6):
        u=rng.normal(size=2**k)+1j*rng.normal(size=2**k)
        if trial==0:u=np.eye(1,2**k,0,dtype=complex).ravel()
        if trial==1:
            u=np.array([0,1,1,0,1,0,0,0],complex)
        u/=la.norm(u)
        v=antistate(u,k)
        U=np.stack([embed(u,k),embed(v,k)],axis=1)
        assert la.norm(U.conj().T@U-np.eye(2))<1e-12
        record,eig,vec,meta,V=hessian(U,k)
        record['trial']=trial;records.append(record)
        np.savez_compressed(PRIVATE/f'hessian-k{k}-trial{trial}.npz',U=U,V=V,eigenvalues=eig,eigenvectors=vec)
        print(json.dumps(record),flush=True)
(PUBLIC/'HESSIAN_CONTROLS.json').write_text(json.dumps({'schema':'finite-zero-tangent-controls-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'finite three-copy rank-two chart; no arbitrary-copy certificate or global optimization','records':records},indent=2)+'\n')
