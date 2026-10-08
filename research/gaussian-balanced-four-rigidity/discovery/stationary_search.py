"""Discovery only: deterministic quadrature of the nine stationary equations.

No numerical output is a proof or an exclusion certificate.
Plackett interpolation computes Gaussian CDFs by one-dimensional quadrature.
"""
import json
import math
import argparse
from pathlib import Path
from hashlib import sha256
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.special import ndtr
from scipy.optimize import least_squares

BASE = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float)
PHI0 = 1 / math.sqrt(2 * math.pi)

def phi2(x, y, r):
    d = 1-r*r
    return math.exp(-(x*x-2*r*x*y+y*y)/(2*d))/(2*math.pi*math.sqrt(d))

def cdf2(h, r):
    return float(ndtr(h[0])*ndtr(h[1]) + quad(
        lambda t: phi2(h[0],h[1],t),0,r,epsabs=2e-10,epsrel=2e-9)[0])

def cdf3(h, R):
    ans = float(np.prod(ndtr(h)))
    for i,j,k in [(0,1,2),(0,2,1),(1,2,0)]:
        rho=R[i,j]
        if abs(rho)<1e-14:
            continue
        def integrand(t):
            r=t*rho
            b=t*np.array([R[k,i],R[k,j]])
            inv=np.array([[1,-r],[-r,1]])/(1-r*r)
            mean=b@inv@h[[i,j]]
            var=1-b@inv@b
            if var<=0:
                raise ValueError("nonpositive conditional variance")
            return rho*phi2(h[i],h[j],r)*float(ndtr((h[k]-mean)/math.sqrt(var)))
        ans += quad(integrand,0,1,epsabs=2e-10,epsrel=2e-9)[0]
    return ans

def values(m, w):
    lam=m@w
    p=[]
    edges=[]
    weights=[]
    for i in range(4):
        others=[j for j in range(4) if j!=i]
        dif=m[others]-m[i]
        lens=np.linalg.norm(dif,axis=1)
        normals=dif/lens[:,None]
        h=(lam[others]-lam[i])/lens
        p.append(cdf3(h,normals@normals.T))
        for j in others:
            if j<i:
                continue
            n=(m[i]-m[j])/np.linalg.norm(m[i]-m[j])
            t=(lam[i]-lam[j])/np.linalg.norm(m[i]-m[j])
            ks=[k for k in range(4) if k not in [i,j]]
            d=m[ks]-m[i]
            tang=d-(d@n)[:,None]*n
            s=np.linalg.norm(tang,axis=1)
            hh=(lam[ks]-lam[i]-(d@n)*t)/s
            r=float(tang[0]@tang[1]/(s[0]*s[1]))
            A=PHI0*math.exp(-t*t/2)*cdf2(hh,r)
            edges.append((i,j))
            weights.append(A/np.linalg.norm(m[i]-m[j]))
    return np.array(p),np.array(weights)

def decode(z):
    T=np.array([[math.exp(z[0]),0,0],[z[3],math.exp(z[1]),0],
                [z[4],z[5],math.exp(z[2])]])
    return BASE@T,np.array(z[6:9])

def residual(z):
    try:
        m,w=decode(z)
        p,weights=values(m,w)
        if min(weights)<=0 or not np.all(np.isfinite(weights)):
            return np.ones(9)*1e3
        return np.r_[4*(p[:3]-.25),np.log(4*weights)]
    except (ValueError,ZeroDivisionError,OverflowError):
        return np.ones(9)*1e3

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--starts',type=int,default=20)
    ap.add_argument('--seed',type=int,default=20261008)
    ap.add_argument('--spread',type=float,default=.65)
    ap.add_argument('--output',default='search.json')
    args=ap.parse_args()
    a=math.sqrt(2)*PHI0/math.pi*math.atan(math.sqrt(2))
    z0=np.r_[np.repeat(math.log(a),3),np.zeros(6)]
    p0,w0=values(*decode(z0))
    assert np.max(np.abs(p0-.25))<1e-9
    assert np.max(np.abs(w0-.25))<1e-9
    rng=np.random.default_rng(args.seed)
    out=[]
    for n in range(args.starts):
        z=z0.copy()
        if n:
            z[:3]+=rng.normal(0,args.spread,3)
            z[3:6]=rng.normal(0,a*args.spread,3)
            z[6:9]=rng.normal(0,args.spread,3)
            z=np.clip(z,np.r_[np.repeat(-7.9,3),np.repeat(-1.9,3),np.repeat(-4.9,3)],
                       np.r_[np.repeat(.9,3),np.repeat(1.9,3),np.repeat(4.9,3)])
        opt=least_squares(residual,z,xtol=1e-10,ftol=1e-10,gtol=1e-10,
                          max_nfev=220,bounds=(np.r_[np.repeat(-8.,3),np.repeat(-2.,3),np.repeat(-5.,3)],
                                               np.r_[np.repeat(1.,3),np.repeat(2.,3),np.repeat(5.,3)]))
        m,w=decode(opt.x)
        row={'start':n,'nfev':opt.nfev,'residual':float(np.max(np.abs(opt.fun))),
             'energy':float(np.sum(m*m)),'apex_norm':float(np.linalg.norm(w)),
             'moments':m.tolist(),'apex':w.tolist()}
        out.append(row)
        print(json.dumps({k:row[k] for k in ['start','nfev','residual','energy','apex_norm']}),flush=True)
        with open(args.output,'w') as f:
            json.dump({'discovery_only':True,'proof_certificate':False,
                       'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
                       'numpy_version':np.__version__,'scipy_version':scipy.__version__,
                       'seed':args.seed,'spread':args.spread,
                       'requested_starts':args.starts,'complete':len(out)==args.starts,
                       'records':out},f,indent=2)

if __name__=='__main__':
    main()
