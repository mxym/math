"""Finite controls, not a substitute for the uniform analytic prime input."""
from itertools import combinations
from math import gcd, isqrt
from collections import Counter
import hashlib

def ck(test):
    if not test:
        raise RuntimeError("control failed")
def primes(n):
    s=[True]*(n+1)
    s[:2]=[False,False]
    for r in range(2,isqrt(n)+1):
        if s[r]:
            s[r*r::r]=[False]*((n-r*r)//r+1)
    return [j for j in range(n+1) if s[j]]
def mul(a,b,mask):
    c=0
    while a:
        lo=a&(-a)
        c ^= b<<(lo.bit_length()-1)
        a ^= lo
    return c&mask
X=1024; mask=(1<<(X+1))-1
plist=primes(X)
tri=0
for m in range(5,32):
    S={a:sum(1<<p for p in plist if p% m==a and p!=2)
       for a in range(m) if gcd(a,m)==1}
    cells={(a,b):mul(S[a],S[b],mask) for a,b in combinations(S,2)}
    for a,b,c in combinations(S,3):
        A,B,C=cells[b,c],cells[a,b],cells[a,c]
        F2=sum(1<<(2*p) for p in plist if p% m==a and p!=2 and 2*p<=X)
        ck(mul(A,F2,mask)==mul(B,C,mask))
        ck((A|B|C)>>(X//2))
        tri+=1
# Genuine CRT translation minor for several different residue patches.
rankcases=0
for ps in [[3],[3,5],[3,5,7],[3,5,7,11]]:
    P=1
    for r in ps: P*=r
    for n in [1,2,4]:
        U=[(P//r)*((n*pow(P//r,-1,r))%r) for r in ps]
        vals=[sum(U[j] for j in range(len(ps)) if m>>j&1) for m in range(1<<len(ps))]
        for a,x in enumerate(vals):
            for b,y in enumerate(vals):
                f=gcd(n+x-y,P)==1
                if a==b: ck(f)
                if b&~a: ck(not f)
        rankcases+=1
# Primitive Gaussian counts from literal lattice points, not the factor formula.
X=2800; Q=241
ps=set(primes(X)); primitive={a for a in range(1,Q) if all(pow(a,240//d,Q)!=1 for d in (2,3,5))}
r2=Counter(x*x+y*y for x in range(-isqrt(X),isqrt(X)+1)
           for y in range(-isqrt(X),isqrt(X)+1) if gcd(x,y)==1 and x*x+y*y<=X)
powers={a*a for a in range(2,isqrt(X)+1)}
for a in range(2,isqrt(X)+1):
    z=a**3
    while z<=X:
        powers.add(z)
        z*=a
ck(not any(n%Q in primitive for n in powers))
N=[n for n in range(1,X+1,4) if n%Q in primitive]
for n in N:
    ck(r2[n]%4==0 and r2[n]//4%4==2*(n in ps))
weighted=Counter(); actual=Counter()
sym=Counter(); off=Counter()
for i,a in enumerate(N):
    for b in N[i:]:
        n=a+b
        if n>X: break
        w=r2[a]*r2[b]//16
        sym[n]+=w*(1+(a!=b))
        if a!=b and a in ps and b in ps: off[n]+=1
        u,v=sorted((a%Q,b%Q))
        if u==v: continue
        key=(n,u,v)
        weighted[key]+=w
        actual[key]+=(a in ps and b in ps)
for k in weighted: ck(weighted[k]%8==4*(actual[k]%2))
for n in range(2,X+1,2):
    t=n//2
    diag=(r2[t]//4)**2 if t in N else 0
    ck((sym[n]-diag)%16==8*(off[n]%2))
print('PASS triangles',tri,'CRT minors',rankcases,'Gaussian labels',len(N),'distinct cell-target fixtures',len(weighted),'symmetric targets',X//2)
