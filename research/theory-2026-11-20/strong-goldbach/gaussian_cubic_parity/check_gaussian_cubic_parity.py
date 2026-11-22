"""Independent finite identities in GaussianCubicParityAtEveryCenter.md.
No finite check claims the asymptotic theorem or a binary-prime lower bound.
Standard library only; works unchanged with python3 -O -B.
"""
from math import gcd, isqrt, comb, prod
from fractions import Fraction as Q
from itertools import product
from collections import Counter

def need(x):
    if not x: raise ArithmeticError("check failed")
def mul(z,w):
    a,b=z; c,d=w
    return ((a*c-b*d)%11,(a*d+b*c)%11)
def power(z,e):
    out=(1,0)
    while e:
        if e&1: out=mul(out,z)
        z=mul(z,z); e//=2
    return out

roots={power((a,b),40) for a,b in product(range(11),repeat=2) if a or b}
need(len(roots)==3 and sum(power((a,b),40)==(1,0) for a,b in product(range(11),repeat=2))==40)
for a,b in product(range(11),repeat=2):
    need(power((a,b),40)==power((-b,a),40))
    need((power((a,b),40)==(1,0))==(power((a,-b),40)==(1,0)))
B=50000
spf=list(range(B+1))
for p in range(2,isqrt(B)+1):
    if spf[p]==p:
        for n in range(p*p,B+1,p):
            if spf[n]==n: spf[n]=p
def factor(n):
    v=[]
    while n>1:
        k=spf[n]; v.append(k); n//=k
    return v
# Enumerate every Gaussian generator modulo its four associates, via quadrant a>0,b>=0.
# Each ideal appears once by PID; compute two times its real cubic phase without using Hecke recurrences.
trace2=[0]*(B+1); norms=[0]*(B+1)
for a in range(1,isqrt(B)+1):
    for b in range(isqrt(B-a*a)+1):
        n=a*a+b*b
        if gcd(n,22)>1: continue
        norms[n]+=1; trace2[n]+=2 if power((a,b),40)==(1,0) else -1
def chi(k): return 0 if k%2==0 else (1 if k%4==1 else -1)
def divisors(n):
    ds={1}
    for q in factor(n): ds.update({d*q for d in ds})
    return sorted(ds)
nsf=hecke=0
for n in range(1,B+1):
    if gcd(n,22)>1: continue
    need(trace2[n]%2==0 and abs(trace2[n])<=2*norms[n])
    need(norms[n]==sum(chi(d) for d in divisors(n)))
    ff=factor(n)
    if len(ff)==len(set(ff)):
        need(trace2[n]==2*prod(trace2[r]//2 for r in ff))
        need(norms[n]==(2**len(ff) if all(r%4==1 for r in ff) else 0))
        nsf+=1
    for d in divisors(n):
        fs=factor(d)
        if len(fs)!=len(set(fs)): continue
        m=n//d
        need(trace2[n]//2==sum((-1)**len(factor(e))*chi(e)*(trace2[d//e]//2)*(trace2[m//e]//2) for e in divisors(gcd(d,m))))
        hecke+=1
# Approximate each ideal-count local density by exact rational truncation of geometric sums.
for r in (3,5,7,13,17,19,29,31):
    z=chi(r)
    invphi=lambda j: Q(1,(r-1)*r**(j-1)) if j else Q(1)
    H=1+Q(z*r,(r-1)*(r-z))
    H1=invphi(1)+H-1
    g=Q(2*r-1,r*r-r+1) if z==1 else Q(1,r*r-r-1)
    need(H*g==H1 and H*(1-g)==1-invphi(1))
    tail=sum(z**j*invphi(j) for j in range(13))+Q(z**13)*invphi(13)/(1-Q(z,r))
    need(H==tail)
def bon(n,k): return sum((-1)**i*comb(n,i) for i in range(min(n,k)+1))
Bcnt=0
for v in product(range(9),repeat=4):
    K=(2,4,6,8)
    U=[bon(n,k) for n,k in zip(v,K)]
    E=sum((comb(v[i],K[i]) if v[i]>=K[i] else 0)*prod(U[j] for j in range(4) if j!=i) for i in range(4))
    need(prod(U)-E<=int(not any(v))<=prod(U)); Bcnt+=1
# Deliberately small, fixed sample cut r>3, not a claim about any effective κ or threshold.
seen=Counter()
for N in range(6000,16001,2):
    b=next(t for t in range(1,44,2) if (N-t)%4==1 and t%11 and (N-t)%11)
    sig=set()
    for p in range(N//3+1,N//2):
        if p%44!=b or spf[p]!=p: continue
        n=N-p; f=factor(n)
        if len(f)!=len(set(f)) or min(f)<=3 or not trace2[n]: continue
        sig.add(1 if trace2[n]>0 else -1)
    seen[tuple(sorted(sig))]+=1
need(seen[(-1,1)]>0)
print("PASS: 40-element kernel,",nsf,"squarefree trace rows,",hecke,"inverse Hecke identities,",Bcnt,"Bonferroni vectors.")
print("Finite illustrative center counts by sign set:",sorted(seen.items()))
