#!/usr/bin/env python3
"""Finite normalization tests; the asymptotic uses the stated theorems."""
from fractions import Fraction as F
from math import isqrt,gcd
from itertools import product
from collections import Counter

def req(ok,msg):
    if not ok:raise ValueError(msg)
def prime(x):return x>=2 and all(x%i for i in range(2,isqrt(x)+1))
I=(F(1,8),F(5,8));K=(F(7,32),F(9,32));L=(F(1,4),F(1,2))
def j(x):return (max(I[0],1-I[1]-x),min(I[1],1-I[0]-x))
def width(A,B):return max(F(0),min(A[1],B[1])-max(A[0],B[0]))
def local(p,s):
    U=range(1,p);nb={r:{u for u in U if (s-r-u)%p} for r in U}
    avg=F(sum(map(len,nb.values())),p-1)
    mass=F(p,p-1)*avg/(p-1)
    if p==2:req(s%2 and mass==2,'two')
    else:
        req(mass==(1-F(1,(p-1)**2) if s%p==0 else 1+F(1,(p-1)**3)),('mass',p,s))
        frac=min(map(len,nb.values()))/avg
        target=F(1) if not s%p else F((p-2)*(p-1),(p-2)*(p-1)+1)
        req(frac==target,'density')
        if p>=5:
            ol=min(F(len(nb[r]&nb[u]),max(len(nb[r]),len(nb[u]))) for r in U for u in U)
            req(ol>=F(1,2),'Doeblin')
        elif s%3:req(sorted(map(len,nb.values()))==[1,2],'three connected')
        else:req(nb=={1:{1},2:{2}},'two sectors')
    return mass
def central(s):
    ps=[p for p in range(3,s) if I[0]*s<=p<=I[1]*s and prime(p)]
    S=set(ps);par={p:p for p in ps}
    def f(p):
        while p!=par[p]:par[p]=par[par[p]];p=par[p]
        return p
    edge=0
    for p in ps:
        for q in ps:
            r=s-p-q
            if p<=q<=r and r in S:par[f(p)]=f(q);par[f(q)]=f(r);edge+=1
    hist=Counter(f(p) for p in ps)
    if not s%3:
        for g in hist:req(len({p%3 for p in ps if f(p)==g})==1,'crossed mod3')
    return s,len(ps),edge,sorted(hist.values(),reverse=True)[:4]
def main():
    # Piecewise-affine endpoint checks on a fine mesh with every breakpoint
    for i in range(129):
        x=I[0]+F(i,128)*(I[1]-I[0])
        req(width(j(x),K)>=F(1,32),'arch overlap')
        if K[0]<=x<=K[1]:req(width(j(x),L)==L[1]-L[0],'common interval')
    cov=[(F(5,2)*m,F(7,2)*m) for m in (F(1,8),F(1,6),F(3,14),F(4,15),F(3,10))]
    req(cov[0][0]<F(3,8) and cov[-1][1]>1 and all(cov[i][1]>cov[i+1][0] for i in range(len(cov)-1)),'dyadic coverage')
    n=0
    for p in range(2,50):
        if prime(p):
            for s in ([1] if p==2 else range(p)):local(p,s);n+=1
    for W in (6,30,210):
        H=[x for x in range(W) if gcd(x,W)==1]
        for s in range(1,W,2):
            mass=F(W,len(H)**3)*sum(gcd(s-x-y,W)==1 for x in H for y in H)
            prod=F(1)
            for p in range(2,W+1):
                if W%p==0 and prime(p):prod*=local(p,s%p)
            req(prod==mass,'CRT edge mass')
    print('arch/dyadic exact; local normalized charts',n,'all odd s mod 6,30,210 checked')
    for s in (10001,10005,10007):print('literal ternary central graph',central(s))
    print('PASS')
if __name__=='__main__':main()
