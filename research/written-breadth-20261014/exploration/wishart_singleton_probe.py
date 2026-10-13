#!/usr/bin/env python3
"""Bounded discovery for full Wishart determinant-product conjecture's singleton subcase.
All outputs are discovery, never proofs of a universal claim.
For W~W_p(2*beta,R/2), the diagonal MGF is det(I-R diag(t))^-beta.
SPD is imposed as R=(1-eps) VV^T+eps I, rows of V unit; beta>(p-1)/2.
"""
import itertools, json, math, time, pathlib
import numpy as np
from scipy.optimize import minimize
from scipy.special import gammaln

ROOT=pathlib.Path(__file__).resolve().parent
OUT=ROOT/'wishart-singleton-discovery-20261014.json'
EPS=1e-6

class Grid:
    def __init__(self, powers, beta):
        self.k=tuple(powers); self.p=len(powers); self.beta=float(beta)
        self.masks=[s for s in range(1,1<<self.p)]
        self.subs=[np.array([j for j in range(self.p) if s>>j&1]) for s in self.masks]
        self.idx=list(itertools.product(*[range(k+1) for k in self.k]))
        self.pos={x:i for i,x in enumerate(self.idx)}
        self.stencils=[]
        for kk in self.idx[1:]:
            ii=next(i for i,a in enumerate(kk) if a)
            usable=[z for z,s in enumerate(self.masks) if all(kk[j]>=1 for j in self.subs[z])]
            prev=[self.pos[tuple(kk[j]-(self.masks[z]>>j&1) for j in range(self.p))] for z in usable]
            fac=[kk[ii]+(self.beta-1)*(self.masks[z]>>ii&1) for z in usable]
            self.stencils.append((np.array(usable),np.array(prev),np.array(fac),kk[ii]))
        self.baseline=math.exp(sum(gammaln(beta+k)-gammaln(beta)-gammaln(k+1) for k in self.k))
    def coeff(self,R,gradient=True):
        q=len(self.masks); vals=np.zeros(q); jac=np.zeros((q,self.p,self.p))
        for z,sub in enumerate(self.subs):
            block=R[np.ix_(sub,sub)]
            ds=(-1)**len(sub)*np.linalg.det(block); vals[z]=ds
            if gradient: jac[z][np.ix_(sub,sub)]=ds*np.linalg.inv(block).T
        f=np.zeros(len(self.idx)); f[0]=1.
        g=np.zeros((len(self.idx),q)) if gradient else None
        for n,(use,prev,fac,den) in enumerate(self.stencils,1):
            fv=f[prev]; weights=fac*vals[use]
            f[n]=-np.dot(weights,fv)/den
            if gradient:
                g[n]=-np.dot(weights,g[prev])/den
                g[n,use]-=fac*fv/den
        if gradient: return f[-1],np.einsum('z,zij->ij',g[-1],jac)
        return f[-1]
    def objective(self,z):
        X=z.reshape(self.p,-1); norms=np.linalg.norm(X,axis=1)
        V=X/norms[:,None]; R=(1-EPS)*(V@V.T)+EPS*np.eye(self.p)
        f,B=self.coeff(R)
        G=(1-EPS)*(B+B.T)@V/self.baseline
        GX=(G-V*np.sum(G*V,axis=1)[:,None])/norms[:,None]
        return f/self.baseline,GX.ravel()

def controls():
    R=np.array([[1,.2,.2],[.2,1,-.9],[.2,-.9,1.]])
    g=Grid((1,1,1),.5)
    assert abs(g.coeff(R,False)-623/2000)<1e-13
    g23=Grid((1,1),.5)
    grouped=.5*g23.coeff(R[1:,1:],False)
    assert abs(g.coeff(R,False)-grouped+2/125)<1e-13
    identity=[]
    for powers,beta in [((2,3,1,2),1.625),((2,2,2,2,2),2.125)]:
        grid=Grid(powers,beta)
        assert abs(grid.coeff(np.eye(len(powers)),False)/grid.baseline-1)<1e-12
        identity.append({'powers':powers,'beta':beta,'ratio':grid.coeff(np.eye(len(powers)),False)/grid.baseline})
    rng=np.random.default_rng(2601014)
    grid=Grid((1,2,3,2),1.625); z=rng.normal(size=(4,6)).ravel()
    val,grad=grid.objective(z); errors=[]
    for j in [0,3,8,13,20]:
        dz=np.zeros_like(z); dz[j]=1e-5
        fd=(grid.objective(z+dz)[0]-grid.objective(z-dz)[0])/(2e-5)
        errors.append(abs(fd-grad[j]))
    assert max(errors)<1e-7
    return {'negative_grouping_control':'exact f111=623/2000, grouped=131/400, gap=-2/125 at beta=1/2; known strong Gaussian failure, not a new conjecture disproof',
            'identity_controls':identity,'gradient_max_absolute_error':max(errors)}

def main():
    t=time.time(); rng=np.random.default_rng(1026142026)
    record={'status':'running_bounded_discovery_only','eps':EPS,'controls':controls(),
            'target':'Full Conjecture 1.1 of Genest-Ouimet-Richards, arxiv:2311.00202v3; singleton determinant blocks suffice to disprove if a legal witness is found',
            'scope':'No positive general assertion; real beta>(p-1)/2 and exact SPD parameterization',
            'runs':[]}
    jobs=[((2,2,2,2),1.625),((1,2,3,4),1.625),((3,3,3,3),1.875),
          ((2,2,2,2,2),2.125),((1,1,2,2,3),2.375),((1,1,1,2,2,2),2.625)]
    for powers,beta in jobs:
        grid=Grid(powers,beta)
        for start in range(5):
            X=rng.normal(size=(grid.p,grid.p+2))
            if start==0:
                X[:,:grid.p]=np.eye(grid.p)+.15*rng.normal(size=(grid.p,grid.p))
                X[:,grid.p:]*=.1
            result=minimize(grid.objective,X.ravel(),jac=True,method='L-BFGS-B',
                            options={'maxiter':100,'ftol':3e-13,'gtol':2e-8,'maxls':20})
            V=result.x.reshape(grid.p,-1); V/=np.linalg.norm(V,axis=1)[:,None]
            R=(1-EPS)*(V@V.T)+EPS*np.eye(grid.p)
            ratio=grid.coeff(R,False)/grid.baseline
            item={'powers':powers,'beta':beta,'degrees_of_freedom':2*beta,'start':start,
                  'ratio':float(ratio),'iterations':int(result.nit),'evaluations':int(result.nfev),
                  'optimizer_success':bool(result.success),'scale_matrix_min_eigenvalue':float(np.linalg.eigvalsh(R)[0]),
                  'R':R.tolist()}
            record['runs'].append(item)
            record['elapsed_seconds']=time.time()-t
            OUT.write_text(json.dumps(record,indent=2)+'\n')
            print(json.dumps({k:item[k] for k in ['powers','beta','start','ratio','iterations']}),flush=True)
            if ratio<1-1e-8:
                record['status']='floating_candidate_requires_independent_exact_certification'
                OUT.write_text(json.dumps(record,indent=2)+'\n')
                return
    record['status']='bounded_discovery_complete_no_violation_found'
    record['elapsed_seconds']=time.time()-t
    OUT.write_text(json.dumps(record,indent=2)+'\n')
    print('DONE',record['status'],'elapsed',record['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
