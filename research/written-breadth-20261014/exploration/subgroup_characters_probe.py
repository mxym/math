"""Discovery only: actual Gram matrices and complete general Lieb target.

Standard alternating split-hook and GL(3,2) character rows are supplied explicitly.
Character orthogonality is a consistency check, not a replacement for proving an
external character table in a final counterexample manuscript.
"""
import itertools,json,math,time,argparse
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

def parity(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def lengths(p):
    seen=set(); out=[]
    for i in range(len(p)):
        if i not in seen:
            j=i;k=0
            while j not in seen: seen.add(j);k+=1;j=p[j]
            out.append(k)
    return sorted(out)
def hook_character(p,k):
    coeff=[1]+[0]*len(p)
    for ell in lengths(p):
        old=coeff[:]
        for j in range(ell,len(coeff)): coeff[j]-=(-1)**ell*old[j-ell]
    return sum((-1)**(k-j)*coeff[j] for j in range(k+1))
def split_cycle_sign(p):
    seq=[0];j=p[0]
    while j!=0:seq.append(j);j=p[j]
    assert len(seq)==len(p)
    return parity(seq)
def alternating_split(N,perms):
    k=(N-1)//2;dim=math.comb(N-1,k)/2
    row=np.zeros(len(perms),dtype=complex)
    for j,p in enumerate(perms):
        if parity(p)==1:
            value=hook_character(p,k)/2
            if lengths(p)==[N]: value+=((1j)**k)*math.sqrt(N)*split_cycle_sign(p)/2
            row[j]=value/dim
    raw=row*dim
    checks={'dimension':dim,'group_order':math.factorial(N)//2,
            'character_norm':float(np.sum(abs(raw)**2)/(math.factorial(N)//2)),
            'character_inner_trivial':float(np.sum(raw).real/(math.factorial(N)//2))}
    assert abs(checks['character_norm']-1)<1e-10
    return row,checks

def gl32_rows(perms):
    vectors=np.array([[(x>>i)&1 for i in range(3)] for x in range(1,8)],dtype=int).T
    lookup={tuple(p):j for j,p in enumerate(perms)}
    data=[]
    for bits in itertools.product([0,1],repeat=9):
        A=np.array(bits,dtype=int).reshape(3,3)
        images=A@vectors%2
        labels=[sum(int(images[i,j])<<i for i in range(3))-1 for j in range(7)]
        if len(set(labels))!=7 or min(labels)<0:continue
        I=np.eye(3,dtype=int);power=A.copy();order=1
        while not np.array_equal(power,I):power=power@A%2;order+=1
        trace=int(np.trace(A)%2)
        data.append((lookup[tuple(labels)],order,trace))
    assert len(data)==168
    rows={}
    tables={
       'GL32_trivial':{1:1,2:1,3:1,4:1,7:1},
       'GL32_degree3':{1:3,2:-1,3:0,4:1},
       'GL32_degree6':{1:6,2:2,3:0,4:0,7:-1},
       'GL32_degree7':{1:7,2:-1,3:1,4:-1,7:0},
       'GL32_degree8':{1:8,2:0,3:-1,4:0,7:1}}
    checks={}
    raws=[]
    for name,table in tables.items():
        dim=table[1];row=np.zeros(len(perms),dtype=complex)
        for j,order,trace in data:
            value=table.get(order)
            if value is None:value=(-1+(1 if trace else -1)*1j*math.sqrt(7))/2
            row[j]=value/dim
        rows[name]=row;raw=row*dim;raws.append(raw)
        checks[name]={'dimension':dim,'group_order':168,
                     'character_norm':float(np.sum(abs(raw)**2)/168),
                     'character_inner_trivial':float(np.sum(raw).real/168)}
        assert abs(checks[name]['character_norm']-1)<1e-10
    raw3=raws[1];raws.insert(2,raw3.conj())
    gram=np.array([[np.vdot(a,b)/168 for b in raws] for a in raws])
    assert np.max(abs(gram-np.eye(6)))<1e-10
    checks['complete_character_orthogonality_error']=float(np.max(abs(gram-np.eye(6))))
    checks['orders']={str(k):sum(o==k for _,o,_ in data) for k in [1,2,3,4,7]}
    return rows,checks

class Problem:
    def __init__(self,N):
        self.N=N
        self.perms=np.array(list(itertools.permutations(range(N))),dtype=int)
        self.rows=np.arange(N)[None,:]
    def pack(self,X):return np.r_[X.real.ravel(),X.imag.ravel()]
    def unpack(self,z,r):return z[:self.N*r].reshape(self.N,r)+1j*z[self.N*r:].reshape(self.N,r)
    def poly(self,C,w):
        entries=C[self.rows,self.perms];val=w@np.prod(entries,axis=1)
        B=np.zeros((self.N,self.N),dtype=complex)
        for i in range(self.N):
            cof=np.prod(np.delete(entries,i,axis=1),axis=1)*w
            np.add.at(B[i],self.perms[:,i],cof)
        return val,B
    def objective(self,z,r,w):
        X0=self.unpack(z,r);norms=np.linalg.norm(X0,axis=1)
        if np.min(norms)<1e-12:return 1e9,np.zeros_like(z)
        X=X0/norms[:,None];C=X@X.conj().T
        P,Bp=self.poly(C,np.ones(len(self.perms)))
        H,Bh=self.poly(C,w)
        if max(abs(P.imag),abs(H.imag))>1e-6 or P.real<0.99:raise RuntimeError('Gram consistency failed')
        P,H=P.real,H.real
        G=-2*((Bh*P-H*Bp)/P**2).T@X
        G=(G-np.real(np.sum(G*X.conj(),axis=1))[:,None]*X)/norms[:,None]
        return -H/P,self.pack(G)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seed',type=int,default=20261014);ap.add_argument('--trials',type=int,default=3)
    args=ap.parse_args();rng=np.random.default_rng(args.seed);t0=time.monotonic()
    report={'date':'2026-10-14','scope':'Discovery for a complete general Lieb counterexample only. No finite search is a proof of dominance.','character_consistency':{},'trials':[],'best':{},'potential_counterexamples':[]}
    for N in [5,7]:
        problem=Problem(N)
        row,checks=alternating_split(N,problem.perms)
        characters={'A'+str(N)+'_split_hook':row}
        report['character_consistency']['A'+str(N)]=checks
        if N==7:
            extra,checks=gl32_rows(problem.perms);characters.update(extra);report['character_consistency']['GL32']=checks
        for name,w in characters.items():
            ranks=[3,4,5] if N==5 else ([4,6,7] if name.startswith('A') else [2,3,4,6,7])
            z0=problem.pack(rng.normal(size=(N,ranks[0]))+1j*rng.normal(size=(N,ranks[0])))
            f,g=problem.objective(z0,ranks[0],w)
            errs=[]
            for j in [0,1,len(z0)//2,len(z0)-1]:
                dz=np.zeros_like(z0);dz[j]=1e-6
                fd=(problem.objective(z0+dz,ranks[0],w)[0]-problem.objective(z0-dz,ranks[0],w)[0])/(2e-6)
                errs.append(abs(fd-g[j]))
            assert max(errs)<2e-6
            best=None
            for r in ranks:
                for trial in range(args.trials):
                    X=rng.normal(size=(N,r))+1j*rng.normal(size=(N,r))
                    if r==N and trial==0:X=np.eye(N,dtype=complex)+0.03*X
                    res=minimize(lambda z:problem.objective(z,r,w),problem.pack(X),jac=True,method='L-BFGS-B',options={'maxiter':500,'ftol':1e-12,'gtol':1e-9})
                    value=-float(res.fun)
                    item={'character':name,'N':N,'rank_embedding':r,'trial':trial,'ratio':value,'iterations':int(res.nit),'converged':bool(res.success)}
                    report['trials'].append(item)
                    if best is None or value>best['ratio']:
                        XX=problem.unpack(res.x,r);XX/=np.linalg.norm(XX,axis=1)[:,None]
                        best=dict(item,gram_rows_real=XX.real.tolist(),gram_rows_imag=XX.imag.tolist(),gradient_check_error=max(errs))
                    if value>1+1e-7:report['potential_counterexamples'].append(best)
                print(name,'embedding',r,'best ratio',max(x['ratio'] for x in report['trials'] if x['character']==name and x['rank_embedding']==r),flush=True)
            report['best'][name]=best
    report['elapsed_seconds']=time.monotonic()-t0
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n')
    print('saved',args.output,'elapsed',report['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
