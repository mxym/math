#!/usr/bin/env python3
"""Exact finite identities and scalar asymptotic checks; no inference code."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, exp, lgamma, log, pi, prod, sqrt

def ring(q,d):
    return tuple(product(range(q),repeat=d))

def mul(a,b,q):
    d=len(a); c=[0]*d
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            s=i+j
            c[s%d]+=(-1 if s>=d else 1)*x*y
    return tuple(x%q for x in c)

def adj(a,q):
    return (a[0],)+tuple(-a[j]%q for j in range(len(a)-1,0,-1))

def plus(a,b,q):
    return tuple((x+y)%q for x,y in zip(a,b))

def sub(a,b,q):
    return tuple((x-y)%q for x,y in zip(a,b))

def dot(a,b,q):
    return sum(x*y for x,y in zip(a,b))%q

# Direct response densities on a finite ternary surrogate, followed by
# exact coordinate marginalization and subset Mobius inversion.
q=3; d=2; T=2; M=4
words=ring(q,d)
responses=tuple(product(range(q),repeat=M))
target=(1,0)
def degree_spectrum(function):
    squares={}
    for k in range(M+1):
        for J in combinations(range(M),k):
            fiber=Counter()
            for y,val in function.items():
                fiber[tuple(y[j] for j in J)]+=val
            mean_sq=sum((v/F(q**(M-k)))**2 for v in fiber.values())/F(q**k)
            squares[J]=mean_sq-sum(squares[K] for r in range(k) for K in combinations(J,r))
    return [sum(x for J,x in squares.items() if len(J)==k) for k in range(M+1)]

fourier_checks=0
for i,a in enumerate(words):
    for b in (words[1],words[(i*5+2)%len(words)]):
        # Reference scalar mass uniform; choose 1/2,1/4,1/4 error law.
        # Relative codeword density is (3/4)^M times a power of 2.
        offsets={s:mul(a,s,q)+mul(b,s,q) for s in words}
        L={}; H={}
        for y in responses:
            l=h=0
            for s,cs in offsets.items():
                w=2**sum(x==z for x,z in zip(y,cs))
                l+=w
                h+=(3*(s[0]==0)-1)*w
            L[y]=F(3,4)**M*l/9-1
            H[y]=F(3,4)**M*h/27
        direct=degree_spectrum(L)
        prop=degree_spectrum(H)
        val=[F(0) for _ in range(M+1)]
        val_h=val[:]
        for u,v in product(words,repeat=2):
            k=sum(x!=0 for x in u+v)
            z=plus(mul(adj(a,q),u,q),mul(adj(b,q),v,q),q)
            if k and z==(0,0):
                val[k]+=F(1,16)**k
            if k and z in ((1,0),(2,0)):
                val_h[k]+=F(1,9)*F(1,16)**k
            fourier_checks+=1
        assert direct==val and prop==val_h

# Explicit condition-on-phase independence with a common fixed nuisance cell.
# Also check the averaged proper-image autocorrelation on a different
# discrete surrogate whose every nonzero Fourier weight is 1/4.
phase_checks=proper_checks=0
for q in (3,5,9,15):
    words=ring(q,2); n=len(words)
    unit_list=[w for w in words if len({mul(w,x,q) for x in words})==n]
    for t,u in enumerate(unit_list[:8]):
        s=words[(t*2+3)%n]
        s2=sub(s,u,q)
        hist=Counter()
        for a in words:
            sa=mul(a,s,q); sa2=mul(a,s2,q)
            for k in words:
                hist[(sub(k,sa,q),sub(k,sa2,q))]+=1
        assert len(hist)==n*n and set(hist.values())=={1}
        phase_checks+=n*n
    for delta in words:
        I={mul(delta,x,q) for x in words}
        if len(I)==1 or len(I)==n:
            continue
        vv=[w for w in words if all(dot(w,x,q)==0 for x in I)]
        assert (1,0) not in vv and (0,1) not in vv
        lhs=sum(prod(F(3+q*(a==0),4) for a in y) for y in I)/len(I)
        rhs=sum(F(1,4)**sum(a!=0 for a in w) for w in vv)
        assert lhs==rhs
        proper_checks+=1

# Counting supports: sampling without replacement and specified row hits.
occupancy_checks=0
for T,d in ((5,2),(6,2),(5,3),(6,3)):
    M=T*d
    for k in range(1,min(8,M)+1):
        row_tot=Counter()
        for I in combinations(range(M),k):
            rows=Counter(j//d for j in I)
            row_tot[tuple(sorted(rows))]+=1
            assert (sum(x==1 for x in rows.values())*2>=k
                    or len(rows)<=3*k//4)
        total=comb(M,k)
        for h in range(1,min(T,k)+1):
            count=sum(v for J,v in row_tot.items() if set(range(h))<=set(J))
            bound=F(prod(range(k-h+1,k+1))*d**h,prod(range(M-h+1,M+1)))
            assert F(count,total)<=bound
            occupancy_checks+=1
        for r in range(1,T+1):
            count=sum(v for J,v in row_tot.items() if len(J)<=r)
            assert F(count,total)<=comb(T,r)*F(r,T)**k
            occupancy_checks+=1

window_checks=0
for q in (3,5,15):
    for t in (log(q)*0.65,log(q)*1.3,log(q)*3):
        lo=0; hi=2*t
        for _ in range(70):
            delta=(lo+hi)/2
            if delta*(1+log(2*t/delta))<log(q):
                lo=delta
            else:
                hi=delta
        delta=(lo+hi)/2
        theta=log(2*t/delta)
        for d in (2048,4096,8192,16384):
            b=0.8/d; T=int(t/b**2); M=T*d; B=2*b*b
            for x in (-0.5,0,1,2):
                D=round(delta*d+log(d)/(2*theta)+x)
                x_d=D-delta*d-log(d)/(2*theta)
                top=sum(log((M-k)*B) for k in range(D))-lgamma(D+1)-d*log(q)
                w=prefix=1
                for k in range(D,max(0,D-100),-1):
                    w*=k/((M-k+1)*B); prefix+=w
                ratio=exp(top)*prefix*sqrt(2*pi*delta)*(1-exp(-theta))*exp(-theta*x_d)
                assert abs(ratio-1)<0.045
                window_checks+=1
# All-target r-th moment: exact diagonal/non-diagonal weighted count.
q=3; words=ring(q,2); n=len(words)
low_weights={w:F(1,16)**sum(x!=0 for x in w[0]+w[1])
             for w in product(words,repeat=2) if 1<=sum(x!=0 for x in w[0]+w[1])<=2}
pens=[]
for a,b in product(words,repeat=2):
    hist=Counter()
    for (u,v),w in low_weights.items():
        z=plus(mul(adj(a,q),u,q),mul(adj(b,q),v,q),q)
        hist[z]+=w
    pens.append(hist)
V=sum(low_weights.values())
lam=max(F(1,len({mul(v,a,q) for a in words})) for v in words if v!=(0,0))
moment_checks=0
for r in range(2,7):
    diagonal=sum(w**r for w in low_weights.values())
    actual=sum(sum(w**r for w in hist.values()) for hist in pens)/len(pens)
    assert diagonal<=actual<=diagonal+lam*(V**r-diagonal)
    moment_checks+=1
print("PASS response Fourier / conditional phase / ideal autocorrelation / occupancy / degree window / all-target moments:",
      fourier_checks,phase_checks,proper_checks,occupancy_checks,window_checks,moment_checks)
