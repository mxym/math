#!/usr/bin/env python3
"""Exact logarithmic-profile, finite-coefficient and rail replay."""
from fractions import Fraction as F
from itertools import product
from math import comb
from random import Random


def ck(ok, detail):
    if not ok:
        raise ArithmeticError(detail)


def subs(n):
    x = n
    while True:
        yield x
        if not x:
            return
        x = (x-1)&n


def branch(es, lift=False):
    # Logarithms in units of 10^-5 log x. Factor labels are distinct even
    # when their logs agree (the same algebra applies to distinct primes).
    vals = [sum(e for i,e in enumerate(es) if s>>i&1) for s in range(1<<len(es))]
    full = (1<<len(es))-1
    h = []
    for s in range(1,full+1):
        r = full^s
        if vals[r] <= 50030:
            continue
        T2 = min(153200-vals[s],183600-2*vals[s],101000)
        if lift:
            T2 = max(T2,100060)
        K = (-1)**r.bit_count()
        Fbig = -sum((-2)**(r^a).bit_count() for a in subs(r) if 2*vals[a]>T2)
        G = 0
        for a in subs(r):
            v = r^a
            if not (8000 <= vals[a] and 8000 <= vals[v] and 2*max(vals[a],vals[v]) <= T2):
                continue
            for c in subs(v):
                b = v^c
                if vals[c]<=20 and b:
                    G+=(-3)**c.bit_count()
        h.append(K-Fbig-G)
    return h


def test_profiles():
    random=Random(4732751)
    zero=giant=four=0
    # Vary total log slightly around 1, representing interior fixed y/x.
    # Use extra forced positive, genuinely tiny factors to hit c>1.
    for rank in [2,3,4,5,6]:
        cases=[]
        for i in range(500):
            total=100000+random.randrange(9)
            pts=sorted(random.sample(range(1,total),rank-1))
            pts=[0]+pts+[total]
            cases.append(tuple(b-a for a,b in zip(pts,pts[1:])))
            if rank>=3:
                for n_tiny in range(1,min(rank-1,3)):
                    tail=tuple(random.randrange(1,21) for _ in range(n_tiny))
                    top=total-sum(tail)
                    p=sorted(random.sample(range(1,top),rank-n_tiny-1))
                    p=[0]+p+[top]
                    cases.append(tail+tuple(b-a for a,b in zip(p,p[1:])))
        cases+=list((
            (24000,23000,25000,28000),
            (20,35000,35000,29980),
            (20,19,39999,59962),
            (55000,20000,5000,20000),
            (19000,5,15000,35995,30000),
        ) if rank==4 else [])
        for es, lift in product(cases,(False,)):
            h = branch(es,lift)
            if len(es)<=3:
                ck(not any(h),("rank<=3",es,lift,h))
                zero+=1
            if max(es)>50500:
                ck(not any(h),("giant",es,lift,h))
                giant+=1
            if len(es)==4:
                ck(all(v<=0 for v in h),("rank4 sign",es,lift,h))
                four+=1
    ck(min(zero,giant,four)>0,"tested effective profiles")
    return zero,giant,four


def check_rails():
    q=F(".504"); r=F(".5003"); t=F(".520"); c=F(".0002"); t0=F(".918"); cap=F(".505")
    a=F(".498")
    ck(q*(1-c)>F(".503"),"opened product upper rail")
    ck(F(".502")>F(".501"),"opened product lower rail")
    ck(F(1,2)+F(".002")/2>F(".5004"),"Fouvry first rail")
    ck(F(4,7)-F(6,7)*F(".003")>F(".5004"),"Fouvry second rail")
    ck(F(".0022")+F(".0981")>F(".10024") and F(".6")*F(".0025")+F(".0983")<F(".09992"),"real opposite Maynard wedge")
    ck(2*q-1+t-a==F(".030"),"M over conductor")
    ck((3*q-1)/3<a/2-F(".060"),"Sharma short interval")
    ck(F(2,3)-F(5,4)*q-F(".030")==F(1,150),"first transformed error")
    ck(1-F(15,8)*q-F(".030")==F(".025"),"second transformed error")
    ck(1-cap+F(".503")==F(".998"),"cap floor margin")
    ck(t0-cap==F(".413") and t0-r==F(".4177"),"cap and lift onset")
    ck(F(".01")+c+F(3,2)*q==F(".7662"),"two-free short-s region")
    ck(sum((-1)**(j-1)*comb(5,j)*comb(j-1,2) for j in range(3,6))==1,"two medium slots")


if __name__=="__main__":
    check_rails()
    print("exact rank <=3, giant, and rank4 cases:",*test_profiles())
    print("all rational rails passed")
