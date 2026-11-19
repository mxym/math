"""Exact illustrative checks; no external packages or assertions disabled by -O."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, combinations
from math import prod,ceil
from collections import defaultdict

def ck(x):
    if not x: raise ArithmeticError("failed exact check")
def inc(v,i):return (v>>i)&1

def transform(atoms, n, a):
    D=len(atoms); p=[F(sum(inc(x,i) for x in atoms),D) for i in range(n)]
    hi=[max(a,v) for v in p];lo=[(1-a)*v/(1-v) if v<a else v for v in p]
    out=defaultdict(F)
    for x in atoms:
        t=[hi[i] if inc(x,i) else lo[i] for i in range(n)]
        cuts=sorted(set([F(0),F(1),a,*t]))
        for s,b in zip(cuts,cuts[1:]):
            m=sum(1<<i for i,v in enumerate(t) if b<=v)
            if b<=a:ck(m&x==x)
            out[m]+=(b-s)/D
    ck(sum(out.values())==1)
    def tail(mask):return sum(v for y,v in out.items() if y&mask==mask)
    ck(all(tail(1<<i)==p[i] for i in range(n)))
    return p,tail,out

def test():
    n=3; count=policies=orth=0
    # Every empirical law from 1,2,3,4 equally weighted atoms on the Boolean cube.
    for d in range(1,5):
        for xs in combinations_with_replacement(range(1<<n),d):
            count+=1
            p,tail,_=transform(xs,n,F(3,4))
            for j in range(1<<n):
                ck(tail(j)>=prod(p[i] for i in range(n) if inc(j,i)));orth+=1
            for a,g in [(F(1),lambda q:F(0)),(F(7,8),lambda q:q/2),
                (F(2,3),lambda q:(1+3*q)/4),
                (F(1,2),lambda q:(1+q)/2),(F(1,4),lambda q:(3+q)/4),
                (F(0),lambda q:F(1)),
                # Discontinuous, nonmonotone: at q=1/3 only, g=1; a=1/3.
                (F(1,3),lambda q:F(q==F(1,3)))]:
                p,tail,_=transform(xs,n,a)
                for i,j in combinations(range(n),2):
                    v,w=sorted((p[i],p[j]));ck(tail((1<<i)|(1<<j))>=v*g(w))
                policies+=1
    xs=[1,2];p,tail,r=transform(xs,2,F(3,4));ck(1-r[0]==F(3,4))
    print("Uniform empirical input laws on 3 bits (1 to 4 atoms):",count)
    print("Upper-orthant checks, including empty/singletons:",orth)
    print("General pairwise-floor transformations, seven envelopes:",policies)
    print("Per-atom common containment, unchanged marginals and sharp 2-bit union: PASS")
if __name__=="__main__":test()
