#!/usr/bin/env python3
"""Exact radical enclosures and rational angular/radial stress tests. No packages."""
from fractions import Fraction as Q
from itertools import product
from math import isqrt
from random import Random
rng=Random(617)
def ck(val,msg):
    if not val:raise ArithmeticError(msg)
def interval_sqrt(x):
    k=10**24
    h=isqrt(x.numerator*k*k//x.denominator)
    lo=Q(h,k);hi=lo if lo*lo==x else Q(h+1,k)
    ck(lo*lo<=x<=hi*hi,"radical interval")
    return lo,hi
def unit(d):
    x=[Q(rng.randrange(-5,6),rng.randrange(1,7)) for _ in range(d-1)]
    norm=sum(v*v for v in x); den=1+norm
    u=[(1-norm)/den]+[2*v/den for v in x]
    ck(sum(t*t for t in u)==1,"rational direction")
    return u
def moment(d,m):
    if m%2:return Q(0)
    p=Q(1)
    for a in range(m//2):p*=Q(2*a+1,2*a+d)
    return p
def main():
    algebra=cases=angular=energy=0
    for r,s in product(range(1,33),repeat=2):
        z=Q(r*r+s*s,2*r*s);k=Q(4*r*s,(r+s)**2)
        ck(1+1/z==1/(1-k/2),"Cauchy/binomial identity")
        for t in (Q(-1),Q(-5,7),Q(0),Q(2,9),Q(1)):
            ck((Q(1,r)+Q(1,s))**2*(r*r+s*s-2*r*s*t)/4==(z+1)*(z-t),"pair symmetrization")
            algebra+=1
    for d in (3,4,5,9):
        for size in (2,4,7):
            for run in range(5):
                us=[unit(d) for i in range(size)];rs=[Q(rng.randrange(1,20),rng.randrange(1,20)) for _ in us]
                Z=Q(0);cost=Q(0)
                pairs=[]
                for i,r in enumerate(rs):
                    for j,s in enumerate(rs):
                        z=(r/s+s/r)/2;t=sum(a*b for a,b in zip(us[i],us[j]))
                        pairs.append((z,t));Z+=z
                        cost+=interval_sqrt((z+1)*(z-t))[1]
                ck(Z==sum(rs)*sum(1/r for r in rs),"star denominator")
                if d==3:
                    ck(3*cost<4*Z,"3D total energy");energy+=1
                for m in range(1,13):
                    mu=moment(d,m);low=Q(0)
                    for z,t in pairs:
                        b=interval_sqrt(1+1/z);c=(t**m-mu)/z**(m-1)
                        low+=c*(b[0] if c>=0 else b[1])
                    ck(low>=0,"centered angular energy with interval lower bound")
                    angular+=1
                cases+=1
    rad=0
    for den in range(1,65):
        for num in range(1,den+1):
            x=Q(num,den);D=1-x
            ck(1-x*x-D*D==2*x*D and 1-x*x>=D*D,"3D closed radial formula sign")
            rad+=1
    print(f'{algebra} exact distance/Cauchy cases; {cases} configurations (exact rational spheres, arbitrary radii), {angular} centered angular energy sums, {energy} 3D total energy comparisons.')
    print(f'{rad} 3D radial endpoint comparisons; all symbolic identities/interval signs PASS.')
if __name__=='__main__': main()
