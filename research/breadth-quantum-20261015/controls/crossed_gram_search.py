"""Unrestricted complex Stiefel search for the exact crossed-Gram ratio.

Homotopies keep local supports full during preconditioning, then release
the barrier. This remains a finite heuristic, never an all-copy proof.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import numpy as np, scipy.linalg as la
import math,datetime,json,time,argparse
PRIVATE=Path('/mnt/d/math/tmp/breadth-quantum-20261015')
PUBLIC=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
exec((PRIVATE/'hessian_zero.py').read_text().split('rng=np.random.default_rng(150615)')[0])
ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=1800);args=ap.parse_args()

def project(U,G):
    M=U.conj().T@G
    return G-U@((M+M.conj().T)/2)

def retract(U):
    Q,R=la.qr(U,mode='economic')
    phases=np.diag(R);phases=phases/np.abs(phases)
    return Q*phases

def local_barrier(U,k):
    n=len(U);grad=np.zeros_like(U);value=0.;mins=[]
    tensor=U.reshape((3,)*k+(2,))
    for i in range(k):
        perm=[i]+[j for j in range(k+1) if j!=i]
        inv=np.argsort(perm);T=tensor.transpose(perm).reshape(3,-1)
        rho=T@T.conj().T/2+np.eye(3)*1e-14
        ev=la.eigvalsh(rho);mins.append(float(ev[0]));value+=float(np.log(ev).sum())
        g=la.solve(rho,T,assume_a='pos')
        grad+=g.reshape((3,)+(3,)*(k-1)+(2,)).transpose(inv).reshape(n,2)
    return value,grad,mins

def objective(U,V,k,mu=0.):
    A1=np.outer(U[:,0],V[:,0].conj());A2=np.outer(U[:,1],V[:,1].conj())
    L1=local_form(A1,(3,)*k,.5);L2=local_form(A2,(3,)*k,.5)
    a=float(np.vdot(A1,L1).real);b=float(np.vdot(A2,L2).real);c=np.vdot(A1,L2)
    assert a>0 and b>0
    if abs(c)<1e-30:return -1e100,(np.zeros_like(U),np.zeros_like(V)),{'a':a,'b':b,'c_abs':abs(c),'log_ratio_squared':-1e100}
    raw=float(2*np.log(abs(c))-np.log(a)-np.log(b));value=raw
    G1=2*(L2/c-L1/a);G2=2*(L1/c.conjugate()-L2/b)
    GU=np.stack([G1@V[:,0],G2@V[:,1]],axis=1)
    GV=np.stack([G1.conj().T@U[:,0],G2.conj().T@U[:,1]],axis=1)
    mi=[]
    if mu:
        bu,bgu,miu=local_barrier(U,k);bv,bgv,miv=local_barrier(V,k)
        value+=mu*(bu+bv);GU+=mu*bgu;GV+=mu*bgv;mi=miu+miv
    return value,(project(U,GU),project(V,GV)),{'a':a,'b':b,'c_abs':float(abs(c)),'c_real':float(c.real),'c_imag':float(c.imag),'log_ratio_squared':raw,'minimum_local_support_eigenvalue':min(mi) if mi else None}

def dot(G,H):return float(sum(np.vdot(g,h).real for g,h in zip(G,H)))

def optimize(U,V,k,mu,stop):
    val,g,meta=objective(U,V,k,mu);direc=g;gn=dot(g,g)
    alpha=1.;iterations=0
    for it in range(1500):
        if time.monotonic()>stop or gn<2e-15:break
        slope=dot(g,direc)
        if slope<1e-10*gn:direc=g;slope=gn
        step=min(alpha,20.)
        for back in range(30):
            Un=retract(U+step*direc[0]);Vn=retract(V+step*direc[1])
            vn,ng,nm=objective(Un,Vn,k,mu)
            if vn>=val+1e-4*step*slope:break
            step*=.5
        else:break
        tg=(project(Un,g[0]),project(Vn,g[1]))
        beta=max(0.,dot(ng,tuple(a-b for a,b in zip(ng,tg)))/max(gn,1e-100))
        nd=(ng[0]+beta*project(Un,direc[0]),ng[1]+beta*project(Vn,direc[1]))
        U,V,val,g,meta,direc=Un,Vn,vn,ng,nm,nd
        gn=dot(g,g);alpha=min(step*1.6,8.)
        iterations=it+1
        if meta['log_ratio_squared']>1e-7:break
    return U,V,meta,iterations,math.sqrt(gn)

rng=np.random.default_rng(151503)
control=[]
for k in [2,3]:
    n=3**k;U=retract(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)));V=retract(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)))
    for mu in [0.,.03]:
        val,g,meta=objective(U,V,k,mu)
        D=(project(U,rng.normal(size=U.shape)+1j*rng.normal(size=U.shape)),project(V,rng.normal(size=V.shape)+1j*rng.normal(size=V.shape)))
        nrm=math.sqrt(dot(D,D));D=tuple(a/nrm for a in D)
        eps=1e-5
        vp=objective(retract(U+eps*D[0]),retract(V+eps*D[1]),k,mu)[0]
        vm=objective(retract(U-eps*D[0]),retract(V-eps*D[1]),k,mu)[0]
        fd=(vp-vm)/(2*eps);an=dot(g,D)
        assert abs(fd-an)<1e-6,(k,mu,fd,an)
        control.append({'k':k,'barrier_mu':mu,'finite_directional_derivative':fd,'analytic':an,'absolute_error':abs(fd-an)})
print(json.dumps({'event':'gradient_controls_passed','controls':control}),flush=True)
start=time.monotonic();stop=start+args.seconds
summary={'schema':'finite-unrestricted-crossed-gram-search-v1','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'runtime_requested_seconds':args.seconds,'scope':'Finite k, all complex two-planes allowed by parametrization. Full-local-support barriers only precondition; zero barrier is released. No global positivity or arbitrary-copy proof.','gradient_controls':control,'records':[],'best':{}}
trial=0
while time.monotonic()<stop:
    k=[3,4,5,3,4][trial%5];n=3**k
    U=retract(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)));V=retract(rng.normal(size=(n,2))+1j*rng.normal(size=(n,2)))
    before=time.monotonic();hom=[]
    for mu in [.03,.003,.0003,0.]:
        U,V,meta,iters,gradnorm=optimize(U,V,k,mu,stop)
        hom.append({'mu':mu,'iterations':iters,'gradient_norm':gradnorm,**meta})
        if meta['log_ratio_squared']>1e-7:break
    final=hom[-1];rec={'trial':trial,'k':k,'homotopy':hom,'seconds':time.monotonic()-before,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    summary['records'].append(rec)
    key=str(k)
    if final['log_ratio_squared']>summary['best'].get(key,{'log_ratio_squared':-1e100})['log_ratio_squared']:
        summary['best'][key]={'trial':trial,**final}
        np.savez_compressed(PRIVATE/f'crossed-gram-best-k{k}.npz',U=U,V=V)
    summary['elapsed_seconds']=time.monotonic()-start
    (PUBLIC/'CROSSED_GRAM_SEARCH.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(rec),flush=True)
    if final['log_ratio_squared']>1e-7:
        summary['negative_candidate_requires_exact_rank2_reconstruction']=True;break
    trial+=1
summary['closed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();summary['complete_target_solved']=False
(PUBLIC/'CROSSED_GRAM_SEARCH.json').write_text(json.dumps(summary,indent=2)+'\n')
