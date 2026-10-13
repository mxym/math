"""Complete Lieb / Marcus block-counterexample discovery, not a partial proof.

Uses H=S_2 wr S_3 <= S_6 with the two unresolved trivial-top linear characters.
A legitimate counterexample for either row would refute GENERAL Lieb dominance.
The trivial-bottom row is the Marcus permanent-of-permanent-blocks conjecture.
"""
import importlib.util,itertools,json,time,argparse
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
src=Path(__file__).with_name('subgroup_characters_probe.py')
spec=importlib.util.spec_from_file_location('probe',src)
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seed',type=int,default=20261014);args=ap.parse_args()
    rng=np.random.default_rng(args.seed);p=mod.Problem(6)
    lookup={tuple(q):j for j,q in enumerate(p.perms)}
    rows={}
    for bottom_sign in [False,True]:
        w=np.zeros(720)
        for blocks in itertools.permutations(range(3)):
            for flips in itertools.product([0,1],repeat=3):
                sigma=tuple(2*blocks[i//2]+((i%2)^flips[i//2]) for i in range(6))
                w[lookup[sigma]]=(-1)**sum(flips) if bottom_sign else 1
        assert np.count_nonzero(w)==48
        rows['wreath_bottom_sign' if bottom_sign else 'Marcus_block_permanent']=w
    t0=time.monotonic();report={'date':'2026-10-14','scope':'Actual PSD Gram discovery; absence of a violation is not a proof.','trials':[],'best':{},'potential_counterexamples':[]}
    for name,w in rows.items():
        best=None
        for r in [2,3,4,5,6]:
            for trial in range(12):
                X=rng.normal(size=(6,r))+1j*rng.normal(size=(6,r))
                if r>=3 and trial<6:
                    base=np.zeros((6,r),dtype=complex)
                    for i in range(6):base[i,i//2]=1
                    X=base+(10**(-trial/2))*X
                if r==6 and trial==6:X=np.eye(6,dtype=complex)+0.01*X
                res=minimize(lambda z:p.objective(z,r,w),p.pack(X),jac=True,method='L-BFGS-B',options={'maxiter':1000,'ftol':1e-14,'gtol':1e-10})
                item={'row':name,'rank_embedding':r,'trial':trial,'ratio':-float(res.fun),'converged':bool(res.success),'iterations':int(res.nit)}
                report['trials'].append(item)
                if best is None or item['ratio']>best['ratio']:
                    XX=p.unpack(res.x,r);XX/=np.linalg.norm(XX,axis=1)[:,None]
                    best=dict(item,gram_rows_real=XX.real.tolist(),gram_rows_imag=XX.imag.tolist())
                if item['ratio']>1+1e-7:report['potential_counterexamples'].append(best)
            print(name,'embedding',r,'max ratio',max(x['ratio'] for x in report['trials'] if x['row']==name and x['rank_embedding']==r),flush=True)
        report['best'][name]=best
    report['elapsed_seconds']=time.monotonic()-t0
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print('saved',args.output,'elapsed',report['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
