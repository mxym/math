#!/usr/bin/env python3
"""Finite probability and analytic sanity checks for the growing-order proof."""
from collections import Counter
from cmath import exp as cexp
from fractions import Fraction as F
from itertools import product
from math import comb, log, pi, sqrt
from random import Random
rng=Random(5)

def bessel(x):
    z=x*x/4
    s0=t0=1.; s1=t1=x/2
    for k in range(1,100):
        t0*=z/(k*k); t1*=z/(k*(k+1))
        s0+=t0; s1+=t1
    return log(s0),s1/s0

bessel_rows=0
for K in (.2,1.,3.,6.,12.):
    grid=[i/80 for i in range(81)]
    ell0=[bessel(K*x)[0] for x in grid]
    ell1=[bessel(K*sqrt(x))[0] for x in grid]
    for j in range(1,80):
        assert ell0[j-1]+ell0[j+1]>=2*ell0[j]-1e-12
        assert ell1[j-1]+ell1[j+1]<=2*ell1[j]+1e-12
        for a in (-1.25,-.2,0.,.4,2.):
            V=ell0[j]-grid[j]*a
            assert V<=grid[j]*(ell0[-1]-a)+1e-12
            bessel_rows+=1

occupancy=0
for n in range(2,6):
    for p in range(2,6):
        for _ in range(8):
            w=[rng.randrange(1,17) for j in range(n)]
            mu=[F(t,sum(w)) for t in w]
            tau=F(1,rng.randrange(2,5))
            J=min(n,int(1/tau)); mass=Counter()
            for T in product(range(n),repeat=p):
                N=Counter(T)
                r=sum(s for s in N.values() if F(s,p)>=tau)
                h=F(r,p)
                assert sum(F(s*s,p*p) for s in N.values())<=h*h+tau
                w0=F(1)
                for j in T: w0*=mu[j]
                mass[r]+=w0
                occupancy+=1
            assert sum(mass.values())==1
            for r,prob in mass.items():
                choices=sum(comb(n,j) for j in range(J+1))
                assert prob<=choices*comb(p,r)*(J*max(mu))**r

coherence=edges=0
for q in (3,5,7,9):
    root=[cexp(2j*pi*k/q) for k in range(q)]
    for d in (4,8):
        for _ in range(25):
            phases=[[rng.randrange(q) for j in range(d)] for a in range(4)]
            w=[rng.randrange(1,30) for a in phases]
            p=[a/sum(w) for a in w]
            M=[sum(p[a]*root[phases[a][j]] for a in range(4)) for j in range(d)]
            S=sum(abs(u)**2 for u in M)/d
            lhs=sum(p[a]*p[h]*sum(root[(phases[a][j]-phases[h][j])%q] for j in range(d))/d
                     for a,h in product(range(4),repeat=2))
            assert abs(S-lhs)<1e-12
            coherence+=1
            # Weight an independent finite circular law at each site.
            W=[[rng.randrange(1,20) for t in range(q)] for j in range(d)]
            P=[[u/sum(row) for u in row] for row in W]
            U=[sum(prob*g for prob,g in zip(row,root)) for row in P]
            T=0.
            for j in range(d):
                h=(j+1)%d; s=-1 if h==0 else 1
                for a in range(4):
                    x,y=phases[a][j],phases[a][h]
                    test=sum(P[j][u]*P[h][v]*root[(u-x-s*(v-y))%q].real
                             for u,v in product(range(q),repeat=2))
                    approx=(U[j]*(U[h].conjugate() if s==1 else U[h])*root[(-x+s*y)%q]).real
                    assert abs(test-approx)<1e-12
                    T+=p[a]*test
                    edges+=1
            assert abs(T)<=sum(abs(z)**2 for z in U)+1e-12

print("PASS Bessel shape / occupancy and mass / coherence / signed edge means:",
      bessel_rows,occupancy,coherence,edges)
