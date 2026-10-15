"""Dense, fully checked finite Hessian to avoid clustered-null ARPACK stalls."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
exec(Path('/mnt/d/math/tmp/breadth-quantum-20261015/zero_extension_hessian.py').read_text().split('rng=np.random.default_rng(151515)')[0])
rng=np.random.default_rng(1516)
records=[]
for k in [5,6]:
    start=time.monotonic();U,W=frames(k,rng);op,C0,V,Z,calls=operator(U,W,k)
    dim=op.shape[0];H=np.empty((dim,dim),float)
    for j in range(dim):
        e=np.eye(1,dim,j).ravel();H[:,j]=op@e
        if j%500==0:print(json.dumps({'event':'assembling','k':k,'column':j,'total':dim,'seconds':time.monotonic()-start}),flush=True)
    symerr=la.norm(H-H.T);assert symerr<1e-9
    eig,vec=la.eigh(H,driver='evd',overwrite_a=True)
    ortherr=la.norm(vec.T@vec-np.eye(dim));assert ortherr<1e-8
    # Full action residual on deterministic random columns plus extremal
    # vectors, evaluated independently through the matrix-free action.
    cols=sorted(set([0,dim-1]+rng.choice(dim,size=20,replace=False).tolist()))
    residuals=[la.norm(op@vec[:,j]-eig[j]*vec[:,j]) for j in cols]
    assert max(residuals)<1e-8
    rec={'k':k,'variables':dim,'q0':q(C0,k),'min_eigenvalue':float(eig[0]),'max_eigenvalue':float(eig[-1]),'negative_count_tol_1e-9':int(np.sum(eig<-1e-9)),'null_count_tol_1e-9':int(np.sum(abs(eig)<1e-9)),'first_positive':float(eig[eig>1e-9][0]),'matrix_symmetry_error':float(symerr),'orthogonality_error':float(ortherr),'checked_action_columns':cols,'max_checked_action_residual':float(max(residuals)),'seconds':time.monotonic()-start,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    np.savez_compressed(PRIVATE/f'zero-dense-k{k}.npz',U=U,W=W,eigenvalues=eig)
    records.append(rec)
    (PUBLIC/'ZERO_DENSE_HESSIAN.json').write_text(json.dumps({'schema':'finite-dense-checked-zero-hessian-v1','scope':'full finite tangent Hessian at one stated qubit zero per k; no full neighborhood or arbitrary-copy theorem','records':records},indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    del H,vec
