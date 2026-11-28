#!/usr/bin/env python3
"""Replay exact small graph budgets, and optionally all eight additional continuous charts."""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import sys
from verify_kissing_nine_160830 import GRAPHS, solve
def require(v):
    if not v: raise RuntimeError('failed exact certificate')
def f(x):return x**4-x*x/4
def cross(r):
    # rational upper rounding of sqrt(3(1-r^2))
    z=3*(1-r*r);d=10**12;s=isqrt(z.numerator*d*d//z.denominator)
    if s*s*z.denominator<z.numerator*d*d:s+=1
    return f((r+Q(s,d))/2)
def captest(T,D,C):
    return C<T and (T-C)**2>(Q(3,4)-T)*(D-T)
def vertices(g,nodes):
    return [(i,j)for i,j in combinations(nodes,2)if g[i]>>j&1]
def static(g,T,hrest):
    n=len(g);E=vertices(g,range(n));out=[]
    for a,b in E:
        B=[i for i in range(n)if i not in [a,b]]
        choices=[]
        for k in range(1,n-1):
            for ss in combinations(B,k):
                if not vertices(g,ss):
                    t=sum(bool((g[a]|g[b])>>i&1) for i in ss)
                    choices.append((Q(3,4*k),Q(t,2*k)))
        choices.append((hrest,Q(1,2)))
        # Minimize a sufficient (upper) strength cutoff at 4 decimal places.
        def close(j):
            c=cross(Q(j,10000))
            return any(d>T and captest(T,d,k*c)for d,k in choices)
        require(close(10000));lo=5000;hi=10000
        while lo+1<hi:
            j=(lo+hi)//2
            if close(j):hi=j
            else:lo=j
        require(close(hi));crit=any(k==0 and d==Q(3,4*((n-3)//2)) for d,k in choices)
        out.append(((a,b),crit,hi))
    return out
def branchlengths(g):
    n=len(g);NB=[{j for j in range(n)if x>>j&1} for x in g];ends=[i for i in range(n)if len(NB[i])!=2];edges=[]
    for i in ends:
        for h in NB[i]:
            prev=i;j=h;d=1
            while j not in ends:
                p=next(iter(NB[j]-{prev}));prev,j=j,p;d+=1
            if i<j:edges.append((i,j,d))
    return sorted(edges)
HARDNEW=[13,37,50,54,58,59,104,112]
def main():
    if not __debug__:raise RuntimeError('run normal Python only')
    if len(sys.argv)>1:
        if sys.argv[1]!='charts':raise SystemExit('usage: verifier.py [charts [class ...]]')
        ids=[int(s) for s in sys.argv[2:]] or HARDNEW
        for j in ids:
            require(j in HARDNEW); print('running class',j,flush=True)
            require(solve(GRAPHS[2][j],159960,150000))
        return
    T7=Q(1960992,10**7);T9=Q(1599666,10**7)
    require(1/(48-Q(1333333+7329707+16542829+17694673,10**6))>T7)
    require(1/(48-Q(1333333+7329707+2*16542829,10**6))>T9>Q(159960,10**6))
    g7=[(1<<((i+1)%7))|(1<<((i-1)%7)) for i in range(7)]
    rr=static(g7,T7,Q(25095,100000))
    require(all(b and r<=9841 for _,b,r in rr))
    for n,T,a in [(7,T7,Q(64898,10**5)),(9,T9,Q(71932,10**5))]:
        m=(n-1)//2
        require((m-1)*Q(4,3)+2/(Q(3,4)+f(a))>1/T)
    g,h=GRAPHS[2][10],GRAPHS[2][44]
    require(branchlengths(g)==[(6,8,3),(6,8,3),(6,8,4)])
    require(branchlengths(h)==[(1,2,2),(1,7,1),(1,8,4),(2,7,1),(2,8,1),(7,8,2)])
    for j,g in [(10,g),(44,h)]:
        rr=static(g,T9,Q(201,1000));require(sum(b for _,b,_ in rr)==6)
        require(max(x[2]for x in rr)<=9994)
        print('class',j,'edge, critical, strict upper cutoff times 10000:',rr)
    print('PASS two graph identifications and all pair bounds')
if __name__=='__main__':main()
