"""Bounded discovery for a counterexample to GENERAL subgroup Lieb dominance.

A found violation in any tested actual PSD Gram matrix would refute the general
conjecture. No absence-of-counterexample statement is a proof. No Lean is run.
"""
import argparse, itertools, json, math, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

N=5
PERMS=np.array(list(itertools.permutations(range(N))),dtype=int)
LOOK={tuple(p):i for i,p in enumerate(PERMS)}
ROWS=np.arange(N)
GROUPS={}
def put(name, affines):
    w=np.zeros(math.factorial(N),dtype=complex)
    for a,b,c in affines:
        p=tuple((a*i+b)%N for i in range(N))
        w[LOOK[p]]=c
    GROUPS[name]=w
put('C5_trivial',[(1,b,1) for b in range(5)])
put('C5_nontrivial',[(1,b,np.exp(2j*np.pi*b/5)) for b in range(5)])
put('D10_trivial',[(a,b,1) for a in [1,4] for b in range(5)])
put('D10_sign',[(a,b,1 if a==1 else -1) for a in [1,4] for b in range(5)])
for k in [0,1,2]:
    put('AGL20_character_'+str(k),[(a,b,(1j)**(k*j)) for j,a in enumerate([1,2,4,3]) for b in range(5)])
ONES=np.ones(math.factorial(N),dtype=complex)

def polynomial_and_matrix_derivative(C, weights):
    entries=C[ROWS[None,:],PERMS]
    terms=np.prod(entries,axis=1)
    value=np.dot(weights,terms)
    B=np.zeros((N,N),dtype=complex)
    for i in range(N):
        cof=np.prod(np.delete(entries,i,axis=1),axis=1)*weights
        np.add.at(B[i],PERMS[:,i],cof)
    return value,B

def unpack(z,r):
    return z[:N*r].reshape(N,r)+1j*z[N*r:].reshape(N,r)
def pack(X):
    return np.r_[X.real.ravel(),X.imag.ravel()]

def objective(z,r,w):
    X0=unpack(z,r)
    norms=np.linalg.norm(X0,axis=1)
    if np.min(norms)<1e-12:
        return 1e9,np.zeros_like(z)
    X=X0/norms[:,None]
    C=X@X.conj().T
    P,Bp=polynomial_and_matrix_derivative(C,ONES)
    H,Bh=polynomial_and_matrix_derivative(C,w)
    if abs(P.imag)>1e-7 or abs(H.imag)>1e-7 or P.real<0.99:
        raise RuntimeError('Actual-object positivity/realness failed')
    P,H=P.real,H.real
    ratio=H/P
    B=(Bh*P-H*Bp)/(P*P)
    G=-2*B.T@X
    G=(G-np.real(np.sum(G*X.conj(),axis=1))[:,None]*X)/norms[:,None]
    return -ratio,pack(G)

def gradient_checks(seed):
    rng=np.random.default_rng(seed)
    X=rng.normal(size=(N,3))+1j*rng.normal(size=(N,3))
    z=pack(X)
    report={}
    for name,w in GROUPS.items():
        val,g=objective(z,3,w)
        errors=[]
        for k in range(len(z)):
            h=1e-6
            dz=np.zeros_like(z); dz[k]=h
            fd=(objective(z+dz,3,w)[0]-objective(z-dz,3,w)[0])/(2*h)
            errors.append(abs(fd-g[k]))
        report[name]=max(errors)
    if max(report.values())>2e-6:
        raise RuntimeError('Analytic gradient failed independent finite differences')
    return report

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--trials',type=int,default=6)
    parser.add_argument('--maxiter',type=int,default=600)
    parser.add_argument('--seed',type=int,default=20261014)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    t0=time.monotonic()
    rng=np.random.default_rng(args.seed)
    gradients=gradient_checks(args.seed)
    results=[]
    Xtran=np.c_[np.ones(N),np.r_[np.sqrt(2)*1j**np.arange(4),0]]
    for name,w in GROUPS.items():
        for r in [2,3,4,5]:
            for trial in range(args.trials):
                X=rng.normal(size=(N,r))+1j*rng.normal(size=(N,r))
                if trial==0:
                    X[:,:2]=Xtran
                    if r>2: X[:,2:]*=0.01
                if trial==1 and r==5:
                    X=np.eye(N,dtype=complex)+0.05*X
                res=minimize(lambda z:objective(z,r,w),pack(X),jac=True,
                             method='L-BFGS-B',options={'maxiter':args.maxiter,'ftol':1e-13,'gtol':1e-9})
                X=unpack(res.x,r)
                X=X/np.linalg.norm(X,axis=1)[:,None]
                C=X@X.conj().T
                P,_=polynomial_and_matrix_derivative(C,ONES)
                H,_=polynomial_and_matrix_derivative(C,w)
                item={'group_character':name,'rank_embedding':r,'trial':trial,
                      'ratio':float(H.real/P.real),'permanent':float(P.real),
                      'generalized_function':float(H.real),'gap':float(P.real-H.real),
                      'converged':bool(res.success),'iterations':int(res.nit),
                      'gram_rows_real':X.real.tolist(),'gram_rows_imag':X.imag.tolist(),
                      'min_eigenvalue_reporting':float(np.linalg.eigvalsh(C)[0])}
                results.append(item)
                if item['ratio']>1+1e-7:
                    print('POTENTIAL_ACTUAL_GRAM_COUNTEREXAMPLE',name,r,trial,item['ratio'],flush=True)
                    break
            best=max(x['ratio'] for x in results if x['group_character']==name and x['rank_embedding']==r)
            print(name,'embedding',r,'best ratio',best,flush=True)
    report={'date':'2026-10-14','client_timezone':'Asia/Shanghai',
            'target':'Disproof of the complete general subgroup permanental-dominance conjecture, using an actual PSD Gram witness if found.',
            'scope':'Discovery only. Finite searches cannot prove dominance for any subgroup or matrix class.',
            'seed':args.seed,'trials_per_case':args.trials,'maxiter':args.maxiter,
            'gradient_max_absolute_errors':gradients,'elapsed_seconds':time.monotonic()-t0,
            'potential_counterexamples':[x for x in results if x['ratio']>1+1e-7],
            'results':results}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print('saved',args.output,'seconds',report['elapsed_seconds'],flush=True)
if __name__=='__main__': main()
