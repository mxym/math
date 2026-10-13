#!/usr/bin/env python3
"""Finite discovery for actual disjoint determinant blocks at noninteger Wishart df.
Exact integer coefficient polynomial is obtained by Wick matchings at all
integer df, then polynomial identity in df from the Wishart MGF. This is a
moment formula, not a proof of the product inequality.
"""
import itertools, json, math, pathlib, time
from collections import defaultdict
import numpy as np
from scipy.optimize import minimize

ROOT=pathlib.Path(__file__).resolve().parent
EPS=1e-6

def matchings(vertices):
    if not vertices:
        yield ()
        return
    a=vertices[0]
    for j in range(1,len(vertices)):
        b=vertices[j]; remain=vertices[1:j]+vertices[j+1:]
        for tail in matchings(remain): yield ((a,b),)+tail

def cycle_count(pairs,n):
    parents=list(range(n))
    def find(x):
        while parents[x]!=x:
            parents[x]=parents[parents[x]]; x=parents[x]
        return x
    for a,b in pairs:
        a=find(a//2); b=find(b//2)
        if a!=b: parents[a]=b
    return len({find(a) for a in range(n)})

def perm_sign(perm):
    return (-1)**sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))

class Formula:
    def __init__(self,sizes):
        self.sizes=tuple(sizes); self.p=sum(sizes)
        self.blocks=[]; off=0
        for d in sizes:
            self.blocks.append(tuple(range(off,off+d))); off+=d
        self.blockof={a:i for i,block in enumerate(self.blocks) for a in block}
        self.variables=[(a,b) for a in range(self.p) for b in range(a+1,self.p) if self.blockof[a]!=self.blockof[b]]
        varid={e:j for j,e in enumerate(self.variables)}
        cache=list((pairs,cycle_count(pairs,self.p)) for pairs in matchings(tuple(range(2*self.p))))
        coefficients=defaultdict(int)
        choices=[list(itertools.permutations(block)) for block in self.blocks]
        for pp in itertools.product(*choices):
            factors=[(a,b) for block,perm in zip(self.blocks,pp) for a,b in zip(block,perm)]
            sign=math.prod(perm_sign(tuple(block.index(v) for v in perm)) for block,perm in zip(self.blocks,pp))
            slots=tuple(i for f in factors for i in f)
            for pairs,cycles in cache:
                mon=[]; dead=False
                for a,b in pairs:
                    i,j=sorted((slots[a],slots[b]))
                    if i==j: continue
                    if self.blockof[i]==self.blockof[j]:
                        dead=True; break
                    mon.append(varid[(i,j)])
                if not dead: coefficients[(cycles,tuple(sorted(mon)))]+=sign
        self.terms=[(cycles,mon,c) for (cycles,mon),c in coefficients.items() if c]
        self.records=[{'df_power':a,'cross_covariance_factors':list(b),'coefficient':c} for a,b,c in self.terms]
        powers=np.zeros((len(self.terms),len(self.variables)),dtype=int)
        for i,(_,mon,_) in enumerate(self.terms):
            for j in mon: powers[i,j]+=1
        self.powers=powers
        self.df_powers=np.array([a for a,_,_ in self.terms])
        self.coeffs=np.array([c for _,_,c in self.terms],float)
        self.jac_idx=np.array(self.variables)
    def evaluate(self,R,df):
        x=np.array([R[a,b] for a,b in self.variables])
        mon=np.prod(x[None,:]**self.powers,axis=1)
        return np.sum(self.coeffs*df**self.df_powers*mon)
    def marginal_product(self,df):
        return math.prod(math.prod(df-j for j in range(d)) for d in self.sizes)
    def matrix_from_parameters(self,z):
        Y=z.reshape(self.p,-1); V=np.empty_like(Y)
        for block in self.blocks:
            ids=list(block)
            Q,_=np.linalg.qr(Y[ids].T,mode='reduced')
            V[ids]=Q.T
        return (1-EPS)*(V@V.T)+EPS*np.eye(self.p)
    def objective(self,z,df):
        R=self.matrix_from_parameters(z)
        return self.evaluate(R,df)/self.marginal_product(df)

def main():
    started=time.time(); rng=np.random.default_rng(1410260710)
    out={'status':'running_bounded_discovery_only','target':'Full determinant Conjecture1.1, arxiv:2311.00202v3',
         'quantifiers':'Any genuine SPD counterexample at real df>p-1 would refute the whole conjecture; positive finite results prove nothing universal',
         'runs':[],'formulas':[]}
    for sizes in [(2,2,2),(3,2,1),(2,2,1)]:
        f=Formula(sizes)
        for df in [f.p-.75,f.p-.25,f.p+.25,10.25]:
            assert abs(f.evaluate(np.eye(f.p),df)/f.marginal_product(df)-1)<2e-12
        formula={'sizes':sizes,'variables':f.variables,'terms':f.records,
                 'source':'Wick matching derivation plus actual Wishart MGF polynomial identity; independent identity-covariance control',
                 'term_count':len(f.terms)}
        out['formulas'].append(formula)
        print('FORMULA',sizes,'terms',len(f.terms),flush=True)
        for df in [f.p-.75,f.p-.25]:
            for start in range(6):
                Y=rng.normal(size=(f.p,f.p+2))
                if start==0:
                    Y[:,:f.p]=np.eye(f.p)+.1*rng.normal(size=(f.p,f.p))
                    Y[:,f.p:]*=.1
                result=minimize(lambda z:f.objective(z,df),Y.ravel(),method='L-BFGS-B',
                                options={'maxiter':100,'ftol':1e-13,'gtol':1e-7,'maxls':20})
                R=f.matrix_from_parameters(result.x)
                item={'sizes':sizes,'degrees_of_freedom':df,'start':start,
                      'ratio':float(f.evaluate(R,df)/f.marginal_product(df)),
                      'min_eigenvalue':float(np.linalg.eigvalsh(R)[0]),
                      'iterations':int(result.nit),'evaluations':int(result.nfev),
                      'optimizer_success':bool(result.success),'R':R.tolist()}
                out['runs'].append(item)
                out['elapsed_seconds']=time.time()-started
                (ROOT/'wishart-block-determinant-discovery-20261014.json').write_text(json.dumps(out,indent=2)+'\n')
                print(json.dumps({k:item[k] for k in ['sizes','degrees_of_freedom','start','ratio','iterations']}),flush=True)
                if item['ratio']<1-1e-8:
                    out['status']='floating_candidate_needs_exact_source_independent_certification'
                    (ROOT/'wishart-block-determinant-discovery-20261014.json').write_text(json.dumps(out,indent=2)+'\n')
                    return
    out['status']='bounded_discovery_complete_no_violation_found'
    out['elapsed_seconds']=time.time()-started
    (ROOT/'wishart-block-determinant-discovery-20261014.json').write_text(json.dumps(out,indent=2)+'\n')
    print('DONE',out['status'],'elapsed',out['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
