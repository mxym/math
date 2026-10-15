from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la, json, datetime
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
src=(PRIVATE/'hessian_zero.py').read_text().split('rng=np.random.default_rng(150615)')[0]
exec(src)

def unpack_chart(z,n):
    ix=0;blocks=[]
    for dim in [(2,2),(n-2,2),(n-2,2)]:
        size=dim[0]*dim[1]
        blocks.append((z[ix:ix+2*size:2]+1j*z[ix+1:ix+2*size:2]).reshape(dim));ix+=2*size
    return blocks

def pack_chart(S,X,Y):
    return np.concatenate([np.stack([A.real,A.imag],axis=-1).ravel() for A in [S,X,Y]])

def polynomials(U,V,z):
    S,X,Y=unpack_chart(z,len(U));VX=V@X;VY=V@Y
    C0=U@U.conj().T
    D=U@S@U.conj().T+VX@U.conj().T+U@VY.conj().T
    E=VX@VY.conj().T+VX@S@U.conj().T+U@S@VY.conj().T
    F=VX@S@VY.conj().T
    return C0,D,E,F

def qcoeff(U,V,z,k):
    Cs=polynomials(U,V,z)
    Ls=[local_form(C,(3,)*k,.5) for C in Cs]
    return [sum(np.vdot(Cs[a],Ls[b]).real for a in range(4) for b in range(4) if a+b==j) for j in range(7)]

rng=np.random.default_rng(1533)
records=[]
for trial in range(6):
    dat=np.load(PRIVATE/f'hessian-k3-trial{trial}.npz')
    U,V=dat['U'],dat['V'];eig,vec=dat['eigenvalues'],dat['eigenvectors']
    null=vec[:,abs(eig)<1e-9];pos=vec[:,eig>1e-9]
    hp=(pos/eig[eig>1e-9])@pos.T
    def f3(z):return qcoeff(U,V,z,3)[3]
    def gradient3(z):
        # f3 is homogeneous cubic: symmetric central difference at unit
        # step has an exact additional f3(e_j), separately subtracted.
        g=np.zeros(len(z))
        for j in range(len(z)):
            e=np.eye(1,len(z),j).ravel()
            g[j]=(f3(z+e)-f3(z-e))/2-f3(e)
        return g
    results=[]
    for sample in range(12):
        z=null@rng.normal(size=null.shape[1]);z/=la.norm(z)
        co=qcoeff(U,V,z,3)
        g=gradient3(z)
        effective=co[4]-.25*g@hp@g
        nullg=la.norm(null.T@g)
        results.append({'sample':sample,'cubic':float(co[3]),'quartic_raw':float(co[4]),'quartic_after_second_order_relaxation':float(effective),'gradient_null_component':float(nullg)})
    record={'trial':trial,'null_dimension':null.shape[1],'samples':results}
    records.append(record)
    print(json.dumps({'trial':trial,'min_effective_quartic':min(r['quartic_after_second_order_relaxation'] for r in results),'max_abs_cubic':max(abs(r['cubic']) for r in results),'max_gradient_null':max(r['gradient_null_component'] for r in results)}),flush=True)
(PUBLIC/'NULL_QUARTIC_CONTROLS.json').write_text(json.dumps({'schema':'finite-null-quartic-control-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'random finite tangent-null directions, not full local or global positivity','records':records},indent=2)+'\n')
