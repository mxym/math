#!/usr/bin/env python3
"""Directed-integer replay for hybrid squarefree covering support bounds."""
from fractions import Fraction as F
from math import isqrt

N=12000
H=18
W=10**42
TABLE=((2,0),(3,1),(4,2),(7,4),(11,8),(19,16),(31,32),(50,64),
       (54,None),(80,128),(97,None),(125,256),(141,None))


def check(c,m):
    if not c:
        raise AssertionError(m)


def primes():
    u=bytearray(b'\x01')*200001
    u[:2]=b'\x00\x00'
    for p in range(2,isqrt(len(u)-1)+1):
        if u[p]:
            u[p*p::p]=b'\x00'*((len(u)-1-p*p)//p+1)
    p=[i for i,a in enumerate(u) if a][:N]
    check(len(p)==N and p[-1]>10*N,'prime cutoff')
    return p


def deltas(ps):
    d={}
    for i,p in enumerate(ps,1):
        a=next((n for hi,n in TABLE if i<=hi),None)
        d[p]=(1,2) if a is None else (a,p)
    return d


def ceildiv(a,b):
    return -(-a//b)


def step(low,high,t,p,dn,dd):
    # t is the admissible singleton count, not the unsifted t-state.
    cnum,cden=dd,dd-dn
    check(0<=t and 0<=2*dn<=dd and cnum<=p*cden,'valid probabilities')
    gr=max(0,t*dd-p*dn)
    now=ceildiv(W*gr,p*cden)
    if t*dd<dn*p:
        knum,kden=p,p-t
    else:
        knum,kden=cnum,cden
    check(knum<=p*kden,'cap probability')
    diff=high-low
    cap=low+ceildiv(diff*knum,p*kden)
    repair=((cnum*kden-knum*cden)*W)//(cnum*kden)
    wide=low+ceildiv(diff*cnum,p*cden)-repair
    return now+max(cap,wide)


def recursion(profile,ds,infinite=True,prefix_keep=0):
    big=1<<H
    A=ceildiv(32*W,16200*N*N) if infinite else 0
    B=C=0
    lo=[A*(1<<(3*s)) for s in range(H)]
    for p in reversed(profile[prefix_keep:]):
        dn,dd=ds[p]
        cnum,cden=dd,dd-dn
        a=(p>=5)
        e=int(p==5)
        check(not a or (big-e)*dd>=p*dn,'affine-cubic tail domain')
        old=lo+[A*big**3+B*big+C]
        lo=[step(old[s],old[s+1],((1<<s)-e) if a else 0,p,dn,dd)
            for s in range(H)]
        # For t>=big the actual comparison has kappa=c. Iterate the
        # cubic-affine continuation coefficients with upward rounding.
        ap=p*cden
        A=ceildiv(A*(ap+7*cnum),ap)
        B=ceildiv(B*(ap+cnum)+(W*cnum if a else 0),ap)
        if a:
            C+=ceildiv(-W*(dd*e+dn*p),ap)
    return lo


def conditional_bans(ps,ds,missing_moduli,cache):
    # Exact early-vector states. Future complete subset counts depend only
    # on active-prefix cardinality once all forbidden moduli are behind us.
    check(all(7<=v<ps[32] for v in missing_moduli),'small modulus limit')
    k=max((i+1 for i,p in enumerate(ps[:32])
           if any(v%p==0 for v in missing_moduli)),default=1)
    if k not in cache:
        cache[k]=recursion(ps,ds,prefix_keep=k)
    tail=cache[k]
    rows=[tail[x.bit_count()] for x in range(1<<k)]
    for i in range(k-1,-1,-1):
        p=ps[i]
        bad=[]
        for a in range(1<<i):
            x=p
            for j in range(i):
                if (a>>j)&1:
                    x*=ps[j]
            if x<7 or x in missing_moduli:
                bad.append(a)
        out=[]
        for a in range(1<<i):
            t=(1<<a.bit_count())-sum((a&b)==b for b in bad)
            out.append(step(rows[a],rows[a+(1<<i)],t,p,*ds[p]))
        rows=out
    return rows[0]


def main():
    ps=primes()
    ds=deltas(ps)
    for p in ps[:10]:
        v=recursion([q for q in ps if q!=p],ds)[0]
        check(v<W,('missing',p))
        print('Set omits',p,': upper',float(F(v,W)),flush=True)
    v=recursion([q for q in ps if q!=31],ds|{37:(8,37),71:(16,71)})[0]
    check(v*1000<999*W,'missing 31 with specialized parameters')
    print('Set omits 31: upper',float(F(v,W)),flush=True)
    trade=((16,2,53,995656),(24,4,89,990494),(47,12,211,997264),
           (89,32,461,999641),(141,64,811,998943),(191,100,1153,999477),
           (314,200,2083,999736),(530,400,3821,999946))
    for m,omit,p,u in trade:
        check(ps[m-1]==p,'endpoint')
        v=recursion(ps[:m-omit]+ps[m:],ds)[0]
        check(v*10**6<u*W,('prefix trade',m,omit))
        print('At least',m-omit+1,'prime factors <=',p,': upper',float(F(v,W)),flush=True)
    from itertools import combinations
    cache={}
    v=conditional_bans(ps,ds,{10,15},cache)
    check(v*10**6<998369*W,'modulus 10 or 15')
    print('Moduli 10,15 both absent: upper',float(F(v,W)),flush=True)
    pool=(10,14,15,21,30,35,42)
    vals=[conditional_bans(ps,ds,set(ban),cache) for ban in combinations(pool,4)]
    check(len(vals)==35 and max(vals)*10**6<975197*W,'small-modulus count')
    print('Any four of 10,14,15,21,30,35,42 absent: max upper',float(F(max(vals),W)),flush=True)


if __name__=='__main__':
    main()
