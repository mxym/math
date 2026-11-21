#!/usr/bin/env python3
"""Exact one-mixed control, including a non-origin modular lift with n a unit."""
from fractions import Fraction as Q
from math import lcm,gcd
def ck(test):
    if not test: raise ValueError('failed exact control')
# Two-variable polynomials (degree in t truncated at m, degree in n unrestricted).
m=7; one={(0,0):1}; t={(1,0):1}; n={(0,1):1}
def add(a,b,f=1):
    o=a.copy()
    for z,v in b.items(): o[z]=o.get(z,0)+f*v
    return {z:v for z,v in o.items() if v}
def mul(a,b):
    o={}
    for (h,j),u in a.items():
        for (k,l),v in b.items():
            if h+k<m: o[h+k,j+l]=o.get((h+k,j+l),0)+u*v
    return {z:v for z,v in o.items() if v}
def powr(a,d):
    v=one
    for _ in range(d):v=mul(v,a)
    return v
# X1^2=n-t, t^3=n-X3, X3^5=n-X4, t X3 X4=n-X1.
x3=add(n,powr(t,3),-1); x4=add(n,powr(x3,5),-1); x1=add(n,mul(t,mul(x3,x4)),-1)
F=add(add(powr(x1,2),t),n,-1)
ck({j:c for (h,j),c in F.items() if h==0}=={1:-1,2:1})
def rem(a):
    o=a.copy()
    for h in range(m):
        while True:
            d=max([j for (i,j) in o if i==h]+[0])
            if d<2:break
            o=add(o,mul({(h,d-2):o[h,d]},F),-1)
    return o
def evalp(a,t,n,mod):
    return sum(v*pow(t,h,mod)*pow(n,j,mod) for (h,j),v in a.items())%mod
p=11; mod=p**m
def lift(z):
    pp=p
    while pp<mod:
        candidates=[z+i*pp for i in range(p) if evalp(F,p,z+i*pp,pp*p)==0]
        ck(len(candidates)==1);z=candidates[0];pp*=p
    return z
origin=lift(0); unit=lift(1)
ck(gcd(unit,p)==1 and origin%p==0)
mons=[];cols=[]
for h in range(m):
    for v in range(2):
        if 2*h+3*v>=2*m:continue
        mon=mul(powr(t,h),powr(x1,v)); mons.append(mon)
        raw=mul(powr(n,m),mon); reduced=rem(raw);cols.append(reduced)
        ck(evalp(reduced,p,origin,mod)==0)
        ck(evalp(raw,p,unit,mod)==evalp(reduced,p,unit,mod))
piv={};kernel=None
for i,col in enumerate(cols):
    vec={u:Q(c) for u,c in col.items()};coef={i:Q(1)}
    while vec:
        u=min(vec);z=vec[u]
        if u not in piv:
            piv[u]=({s:c/z for s,c in vec.items()},{s:c/z for s,c in coef.items()})
            break
        d,k=piv[u]
        for dest,src in [(vec,d),(coef,k)]:
            for s,c in src.items():
                dest[s]=dest.get(s,0)-z*c
                if not dest[s]: del dest[s]
    else:
        if kernel is None:
            den=lcm(*(q.denominator for q in coef.values()))
            kernel={s:int(q*den) for s,q in coef.items()}
ck(len(piv)<=m and kernel)
raw={}
for i,c in kernel.items(): raw=add(raw,mons[i],c)
ck(not rem(mul(powr(n,m),raw)))
ck(evalp(raw,p,unit,mod)==0)
# Signature coverage: the beta=2 boundary shares only its immediately preceding exponent.
seen=0;eq=0
from itertools import product
for k in [3,4,5]:
    for aa in product(range(2,9),repeat=k-1):
        if any(gcd(x,y)>1 for i,x in enumerate(aa[:-1]) for y in aa[:i]):continue
        B=aa[-1]
        for i,q in enumerate(aa[:-1]):
            g=gcd(q,B)
            if g==1:continue
            for b in range(1,B+1):
                M=B//g; gamma=max(Q(B,aa[i+1]),Q(B,aa[0])-b)
                s=M-B+gamma
                ck(s<=0)
                if s==0:
                    ck(B==2 and g==2 and i==k-3 and b>=M);seen+=1
                if b<M:
                    h=M//b; R=Q(1)
                    for j in range(h+1):R*=Q(j*g+1,g*(j+1))
                    ck(h>=1 and 0<R<Q(1,g) and s<0)
                    if M-b*(h+1)==s:eq+=1
print('4 labels / 3 distinct factors in mixed row; columns, rational rank, kernel terms =',len(cols),len(piv),len(kernel))
print('Hensel lifts modulo 11^7: origin',origin,'unit',unit,'; independent exact evaluations PASS')
print('small residual beta=2 boundaries and equal-order tests =',seen,eq)
