#!/usr/bin/env python3
"""Small exact controls for the pure-row formal-origin and integer projector."""
from functools import lru_cache
from itertools import product
from fractions import Fraction
from math import gcd,lcm,prod

def ck(x, msg):
    if not x: raise ValueError(msg)

def conv(x,y,m):
    z=[0]*m
    for i in range(m):
        for j in range(m-i): z[i+j]+=x[i]*y[j]
    return z

def run(a,m,need_kernel=False,point=None):
    k=len(a); D=prod(a); box=list(product(*(range(ai) for ai in a))); zero=(0,)*k
    weight=lambda v: sum(vi*(D//ai) for vi,ai in zip(v,a))
    ck(len({weight(v)%D for v in box})==D,'CRT')
    ids={v:i for i,v in enumerate(box)}
    # Independent formal series: recompute each coefficient from known lower orders.
    X=[[0]*m for _ in a]
    for n in range(1,m):
        for i,ai in enumerate(a):
            z=[1]+[0]*(m-1)
            for T in range(ai): z=conv(z,X[i],m)
            X[(i+1)%k][n]=(n==1)-z[n]
    ev=[]
    for v in box:
        z=[1]+[0]*(m-1)
        for i,vi in enumerate(v):
            for T in range(vi): z=conv(z,X[i],m)
        ev.append(z)
    @lru_cache(None)
    def reduce(j,v):
        if j>=m: return {}
        for i,ai in enumerate(a):
            if v[i]>=ai:
                h=list(v);h[i]-=ai
                ret=reduce(j+1,tuple(h)).copy()
                h[(i+1)%k]+=1
                for u,c in reduce(j,tuple(h)).items(): ret[u]=ret.get(u,0)-c
                return {u:c for u,c in ret.items() if c}
        return {j*D+ids[v]:1}
    E=[]; mons=[]
    for j in range(m):
        for v in box:
            if j*D+weight(v)>=m*D: continue
            h=list(v);h[0]+=m
            col=reduce(j,tuple(h)); E.append(col); mons.append((j,v))
            vals=[0]*m
            for u,c in col.items():
                l,b=divmod(u,D)
                for o,val in enumerate(ev[b][:m-l]): vals[l+o]+=c*val
            ck(not any(vals),'formal origin')
            ck(all(abs(c)<=2**(m+D) for c in col.values()),'coefficient growth')
    if not need_kernel:
        return len(E)
    # Rational column elimination, tracking the FIRST exact dependency and primitive numerator.
    piv={}
    for t,col in enumerate(E):
        vec={u:Fraction(c) for u,c in col.items()}; coef={t:Fraction(1)}
        while vec:
            u=min(vec); v=vec[u]
            if u not in piv:
                piv[u]=({s:c/v for s,c in vec.items()},{s:c/v for s,c in coef.items()})
                break
            red,track=piv[u]
            for s,c in red.items():
                vec[s]=vec.get(s,0)-v*c
                if not vec[s]: del vec[s]
            for s,c in track.items():
                coef[s]=coef.get(s,0)-v*c
                if not coef[s]: del coef[s]
        else:
            b=lcm(*(c.denominator for c in coef.values()))
            ico={s:int(c*b) for s,c in coef.items()}
            g=gcd(*ico.values());ico={s:c//g for s,c in ico.items()}
            check={}
            for s,c in ico.items():
                for u,d in E[s].items(): check[u]=check.get(u,0)+c*d
            ck(all(d==0 for d in check.values()) and ico,'exact integer kernel')
            if point:
                N,z=point
                ck(all(z[i]**ai+z[(i+1)%k]==N for i,ai in enumerate(a)),'fixture')
                ck(gcd(N,z[0])==1,'primitive')
                val=sum(c*N**mons[s][0]*prod(x**n for x,n in zip(z,mons[s][1])) for s,c in ico.items())
                ck(val%N**m==0,'integer projector')
                print('at known center',N,': P/N^m =',val//N**m)
            return len(E),len(ico),max(abs(c) for c in ico.values())
    raise ValueError('no exact dependency')

print('2,3 control',run((2,3),7,True))
print('3,7 positive control',run((3,7),8,True,(2200,(13,3))))
print('2,3,5 formal columns',run((2,3,5),7))
print('PASS')
