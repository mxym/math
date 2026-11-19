"""Exact finite checks; no test constitutes proof of the infinite theorem."""
from collections import Counter
from fractions import Fraction as F
from math import gcd

def need(flag):
    if not flag: raise RuntimeError("certificate check failed")

def atoms(x):
    if not x: return []
    q=x.denominator; need(q&(q-1)==0)
    return [F(1<<j,q) for j in range(x.numerator.bit_length()) if (x.numerator>>j)&1]

aff=0
for s in range(10):
    r=F(1,1<<s)
    states={}
    for k in range(2):
        x=F(k,2)
        p=(1-r)/2+r*((x+F(1,2))**2-x**2)
        a=atoms(p)
        states[k]=[(v,'T' if j==0 else 'U') for j,v in enumerate(a)]
    for n in range(1,9):
        new={}
        h=F(1,1<<n)
        for k,L in states.items():
            x=k*h; p=(1-r)*h+r*((x+h)**2-x**2)
            need(sorted(v for v,_ in L)==atoms(p))
            need([v for v,T in L if T=='T']==[r*h*h])
            aff+=1
            for bit in (0,1):
                A=[]
                for v,T in L:
                    if T=='U': A.append((v/2,'U'))
                    else:
                        A.append((v/4,'T'))
                        if bit:A.append((v/2,'U'))
                new[2*k+bit]=A
        states=new

modrows=0
for B in range(2,48):
    D=B
    while D%2==0:D//=2
    if D==1:continue
    H=(D-1).bit_length()
    for A in range(1,B):
        if gcd(A,B)!=1:continue
        q=F(2*B-A,4*B).denominator
        need(q&(q-1)!=0)
        for n in range(1,5):
            for k in range(1<<n):
                m=n+H
                hits=[q for q in range(k<<H,(k+1)<<H) if (((B-A)<<m)+2*A*q+A)%D==0]
                need(len(hits)>0);modrows+=1

cub=0; carry=0
def cubic(n,k):return F((k+1)**3-k**3,1<<(3*n))
def pack(kids):
    c=Counter(x for a in kids for x in a);z=[]
    while c:
        w=min(c);a=c.pop(w)
        if a%2:z.append(w)
        if a//2:c[2*w]+=a//2
    return z
for N in range(2,9):
    h=F(1,1<<N);g=F(1,1<<(N//2)); totalR=F()
    for k in range(1<<N):
        lo=3*(k*h)**2; hi=3*((k+1)*h)**2
        a=(lo//g)*g
        if hi>a+g:a=F()
        R=cubic(N,k)-h*a
        ell=atoms(h*a)
        need(sorted(ell+atoms(R))==atoms(cubic(N,k)))
        weights=(3*k*k-a/h**2,3*k,1)
        need(min(weights)>=0 and all(F(w).denominator==1 for w in weights))
        need(sum(weights)*h**3==R)
        for m in range(6):
            v=1<<m
            for j in range(v):
                p=cubic(N+m,k*v+j)
                sub=p-h*a/v
                acc=sum(w*F((j+1)**d-j**d,v**d) for d,w in enumerate(weights,1))
                need(sub==acc*h**3)
                need(sorted([w/v for w in ell]+atoms(sub))==atoms(p))
                cub+=1
        totalR+=R
        kids=[atoms(cubic(N+1,2*k+b)) for b in (0,1)]
        need(sorted(pack(kids))==atoms(cubic(N,k)));carry+=1
    need(totalR<=g+9*h/g)
print(f"PASS: {aff} affine prefix decompositions; {modrows} residue-block hitting tests; {cub} cubic descendant locks and exact residual mixtures; {carry} binary carry refinements.")
