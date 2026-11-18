"""Author checks for integer-step cosets and binomial residues; stdlib only."""
from itertools import product
from collections import Counter
from math import comb,gcd,prod
from fractions import Fraction as F
from random import Random
def need(p,msg):
    if not p:raise ArithmeticError(msg)
def bvec(n):return [comb(n,j) for j in range(n+1)]
def checklines():
    # Use invariant coordinates to label the full cosets (integer multiples of the step),
    # not the entire real line: record first coordinate modulo step as well.
    for_n=range(1,11);count=0
    for n,m,b,a in product(for_n,for_n,range(1,9),range(1,9)):
        p,q=bvec(n),bvec(m);mass=Counter()
        for i,j in product(range(n+1),range(m+1)):
            mass[(a*i-b*j,i%b)]+=p[i]*q[j]
        need(9*len(mass)*max(mass.values())**2<=8*4**(n+m),'8/9 line')
        count+=1
    print('PASS 8/9 line bound incl. nonprimitive projected steps:',count)
    r=Random(41)
    for s in range(2,9):
        for trial in range(18):
            n=[r.randrange(1,4) for _ in range(s)];h=[r.randrange(1,5) for _ in range(s)]
            bs=list(map(bvec,n));mass=Counter()
            for z in product(*(range(k+1) for k in n)):
                i=z[0]
                key=(i%h[0],)+tuple(h[0]*z[j]-h[j]*i for j in range(1,s))
                mass[key]+=prod(col[k] for col,k in zip(bs,z))
            k=len(mass);v=prod(j+1 for j in n)
            need(k==v-prod(max(0,j+1-l) for j,l in zip(n,h)),'higher rank-one subgroup count')
            need(k*max(mass.values())**2<=4**sum(n),'higher dimensional fibers')
    print('PASS 126 higher-box instances including the critical s=3,4')
def aux():
    dct=0
    for d in range(2,54):
        for l in (d,2*d,2*d+1):
            r=[0]*d
            for x,w in enumerate(bvec(l)):r[x%d]+=w
            q=F(max(r),2**l)
            if l==d:need(q==F(max(bvec(d)),2**d),'modulo first')
            if l==2*d:need(q==F(comb(2*d,d)+2,4**d),'autocorrelation')
            if l>=2*d:need(d*q*q<=F(1,2) and (d==2 or d*q*q<=F(3,8)),'cap')
            dct+=1
    print('PASS modulo-binomial tests:',dct)

if __name__=='__main__':checklines();aux()
