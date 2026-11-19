"""Exact six-point shaking certificate, no prime field or floating-point arithmetic.
Requires NumPy only for matrix operations on Python arbitrary-precision integers
(dtype=object). The bound itself has no probabilistic numerical step.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import factorial, prod, lcm, comb
import numpy as np

def require(p,msg):
    if not p: raise ArithmeticError(msg)
N=4
DEG=15
SCALE=factorial(4)*factorial(5)**2
def multip(a,b):
    z=defaultdict(int)
    for k,v in a.items():
        for j,w in b.items():z[tuple(sorted(k+j))]+=v*w
    return z

def values(gap):
    x=[0]
    for d in gap:
        require(type(d) is int and d>0,"bad gap")
        x.append(x[-1]+d)
    require(len(x)==6,"need five gaps")
    spans=[x[c]-x[a] for a in range(6) for c in range(a+2,6)]
    D=prod(spans)*(x[5]-x[0])
    unit=lcm(*spans)*12
    @lru_cache(None)
    def comb_poly(seq,side):
        m=len(seq)-2
        if m==0:return {():1}
        a,c=seq[0],seq[-1];z=defaultdict(int)
        weight,rem=divmod(unit,m*(x[c]-x[a]));require(not rem,"local scale")
        for pos in range(1,m+1):
            j=seq[pos];lin={}
            if a==0:lin[(side*6,)]=weight*(x[c]-x[j])
            if c==5:lin[(side*6+1,)]=weight*(x[j]-x[a])
            for i in range(a+1,c):
                lin[(side*6+1+i,)]=weight*(x[min(i,j)]-x[a])*(x[c]-x[max(i,j)])
            for key,v in multip(lin,multip(comb_poly(seq[:pos+1],side),comb_poly(seq[pos:],side))).items():z[key]+=v
        return z
    z=defaultdict(int)
    for bits in product((False,True),repeat=4):
        def side(b): return tuple([0]+[i+1 for i,s in enumerate(bits) if s==b]+[5])
        for k,v in multip(comb_poly(side(True),0),comb_poly(side(False),1)).items():
            a,b,c,d=[k.count(i) for i in (0,6,1,7)]
            beta_num=factorial(5)**2*prod(factorial(r) for r in (a,b,c,d))
            beta,rem=divmod(beta_num,factorial(a+b+1)*factorial(c+d+1));require(not rem,"beta scale")
            key=tuple(sorted(0 if i==6 else 1 if i==7 else i for i in k))
            z[key]+=v*beta
    m={}
    for key,v in z.items():
        w,r=divmod(v*factorial(4)*D,unit**4);require(not r,"overall integer scale")
        m[key]=w
    return m

def delta(z):
    m=z.copy()
    for key,v in z.items():
        if max(key)>=8:continue
        for bs in product((0,1),repeat=sum(i>=2 for i in key)):
            it=iter(bs)
            j=tuple(sorted(i+6*next(it) if i>=2 else i for i in key))
            m[j]-=v
    return m

def grid():
    return [(a,b,c,d) for a in range(DEG+1) for b in range(DEG+1-a) for c in range(DEG+1-a-b) for d in range(DEG+1-a-b-c)]
def interpolate(pts,m):
    # Evaluate on (1+node) in four variables (fifth gap fixed to one).
    # First take all four finite differences, then convert the resulting
    # falling-factorial basis to the monomial basis along the four axes.
    for stage in (0,1):
        for ax in range(4):
            lines=defaultdict(list)
            for ix,idx in enumerate(pts):lines[idx[:ax]+idx[ax+1:]].append((idx[ax],ix))
            for line in lines.values():
                seq=sorted(line);L=len(seq);idx=[j for _,j in seq]
                require([j for j,_ in seq]==list(range(L)),"irregular lower set")
                M=np.zeros((L,L),dtype=object)
                if stage==0:
                    for j in range(L):
                        for t in range(j+1):M[j,t]=(-1)**(j-t)*comb(j,t)
                    v=M@m[idx]
                    for j in range(L):
                        if j>1:require(all(t%factorial(j)==0 for t in v[j]),"nonintegral Newton coefficient")
                        v[j]=v[j]//factorial(j)
                    m[idx]=v
                else:
                    w=[1]
                    for j in range(L):
                        M[:j+1,j]=w
                        w=[b-(j+1)*a for a,b in zip(w+[0],[0]+w)]
                    m[idx]=M@m[idx]
    return m
def main():
    pts=grid(); require(len(pts)==3876,"incorrect node count")
    z0=values((1,)*5)
    keys=sorted(k for k in z0 if any(2<=a<=5 for a in k) and any(a>=8 for a in k))
    require(len(z0)==715 and len(keys)==468,"incorrect term count")
    m=np.empty((len(pts),len(keys)),dtype=object)
    for i,t in enumerate(pts):
        z=delta(values(tuple(1+j for j in t)+(1,)))
        require(len(z)==715 and all(v==0 for k,v in z.items() if not(any(2<=a<=5 for a in k) and any(a>=8 for a in k))),"unaccounted monomial")
        m[i]=[z[k] for k in keys]
    interpolate(pts,m)
    require(not np.any(m<0),"negative coefficient")
    require(np.all(m.sum(axis=0)>0),"identically zero mixed coefficient")
    require(np.array_equal(m.sum(axis=0),[delta(z0)[k] for k in keys]),"at-one replay mismatch")
    positive=int(np.count_nonzero(m)); largest=int(m.max())
    print(f"PASS: {len(keys)} curvature coefficients; {len(pts)} abscissa monomials each; {positive} positive, {m.size-positive} zero, no negative; largest {largest}")
if __name__=="__main__":main()
