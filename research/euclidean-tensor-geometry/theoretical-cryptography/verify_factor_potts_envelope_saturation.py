
"""Exact rational checks for the Potts saturation constructions and overlap."""
from fractions import Fraction as F
from itertools import product
from random import Random

def unit(q,k):
    return tuple(F(int(i==k)) for i in range(q))

def uniform_on(q,k):
    return tuple(F(int(i<k),k) for i in range(q))

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))

def interpolate(a,x,y):
    return tuple((1-a)*u+a*v for u,v in zip(x,y))

def normalize(x):
    return [F(y,sum(x)) for y in x]

def main():
    rng=Random(98021)
    exact=0
    for q in range(3,16):
        u=uniform_on(q,q)
        for k in range(1,q):
            # A capped-simplex vertex is a nested two-support mixture.
            for a in (F(j,19) for j in range(20)):
                w=interpolate(a,uniform_on(q,k),uniform_on(q,k+1))
                b=(1-a)/k+a/(k+1)
                assert w==(b,)*k+(a/(k+1),)+(F(0),)*(q-k-1)
                assert sum(w)==1 and max(w)==b
                if 0<a<1: assert F(1,k+1)<b<F(1,k)
                exact+=1
        # Lower-profile fixed-prior construction, including zero active weights.
        for _ in range(300):
            t=F(rng.randrange(1,21),20)
            beta=F(rng.randrange(1,21),20)
            heavy=normalize([rng.randrange(1,5)]+[rng.randrange(5) for _ in range(q-1)])
            pi=tuple((1-beta*t)/q+beta*t*w for w in heavy)
            rows=[interpolate(t,u,unit(q,j)) for j in range(q)]
            expected=tuple((1-beta)*u[i]+sum(beta*heavy[j]*rows[j][i]
                           for j in range(q)) for i in range(q))
            assert pi==expected and sum(pi)==1
            assert sum(p>(1-beta*t)/q for p in pi)==sum(w>0 for w in heavy)
            assert min(pi)>=(1-beta*t)/q
            exact+=1
        # Shared outputs and squared-overlap formula, including the zero diagonal.
        for lam in [F(-1,q-1), F(-1,2*(q-1)), F(1,4), F(3,4)]:
            rows=[interpolate(lam,u,unit(q,j)) for j in range(q)]
            assert all(min(r)>=0 and sum(r)==1 for r in rows)
            for a,b in product(range(q),repeat=2):
                assert any(x*y>0 for x,y in zip(rows[a],rows[b]))
                assert dot(rows[a],rows[b])==(1-lam**2)/q+(lam**2 if a==b else 0)
                exact+=1
        # Extremal two-support decomposition for heavy p>=1/2.
        for j in range(1,20):
            p=F(20+j,40)
            tail=normalize([rng.randrange(1,6) for _ in range(q-1)])
            prior=(p,*((1-p)*w for w in tail))
            pair_mixture=[interpolate(1-p,unit(q,0),unit(q,i)) for i in range(1,q)]
            reconstructed=tuple(sum(w*pair[i] for w,pair in zip(tail,pair_mixture))
                                for i in range(q))
            assert prior==reconstructed and max(prior)==p
            exact+=1
    print("PASS exact rational saturation/overlap checks",exact)

if __name__=="__main__":
    if not __debug__: raise RuntimeError("run without python -O")
    main()
