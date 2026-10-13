"""Exploration only: alternating row maximization, never a proof premise."""
import itertools, json
import numpy as np

PERMS = np.array(list(itertools.permutations(range(4))))
SIGNS = np.array([(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4)) for p in PERMS])
RNG = np.random.default_rng(20261013)

def value(a, z):
    terms = np.prod(a[np.arange(4)[None,:], PERMS], axis=1)
    return terms.sum(), (terms*SIGNS).sum()

def maximize(z, starts=160):
    weight = 1+z*SIGNS
    best = (-1,None)
    for _ in range(starts):
        a = RNG.normal(size=(4,4))+1j*RNG.normal(size=(4,4))
        a /= np.linalg.norm(a,axis=1)[:,None]
        prev = 0
        for it in range(1200):
            for i in range(4):
                others = [k for k in range(4) if k!=i]
                coeff = weight*np.prod(a[np.array(others)[None,:], PERMS[:,others]],axis=1)
                v = np.array([coeff[PERMS[:,i]==j].sum() for j in range(4)])
                a[i] = np.conj(v)/np.linalg.norm(v)
            per,det = value(a,z)
            obj=abs(per+z*det)
            if abs(obj-prev)<2e-13: break
            prev=obj
        if obj>best[0]: best=(obj,a.copy())
    obj,a=best
    per,det=value(a,z)
    candidates = [1.5,abs(1+z),abs(1-z),abs(z+1j/np.sqrt(3)),abs(z-1j/np.sqrt(3))]
    return dict(z=[z.real,z.imag],maximum=obj,candidate=max(candidates),per=[per.real,per.imag],det=[det.real,det.imag],matrix=np.stack([a.real,a.imag],axis=-1).tolist(),gram_absolute=np.abs(a@a.conj().T).tolist())

if __name__=='__main__':
    results=[]
    for z in [0.5j,1j,2j,4j,0.5+0.5j,1+1j,2+1j,0.2+1j]:
        r=maximize(z)
        results.append(r)
        print(json.dumps(r),flush=True)
    with open('explore_pencil.json','w') as f: json.dump(results,f,indent=2)
