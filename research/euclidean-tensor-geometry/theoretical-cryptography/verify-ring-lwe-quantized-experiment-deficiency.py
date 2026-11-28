#!/usr/bin/env python3
"""Exact tent interpolation identities and finite checks of the local window constants."""
from fractions import Fraction as F
from math import cos, erf, log, pi, sin, sqrt
from random import Random

# For c(theta)=1/24+theta/2-theta^2/2, integrate the exact square.
c=[F(1,24),F(1,2),F(-1,2)]
assert sum(x*y/F(i+j+1) for i,x in enumerate(c) for j,y in enumerate(c))==F(49,2880)
assert 32*sum(x*y/F(i+j+1) for i,x in enumerate(c) for j,y in enumerate(c))==F(49,90)

rng=Random(620)
shifts=0
for m in (3,5,6,9,10,15,21,27,45):
    f=[F(rng.randrange(1,10),6) for j in range(m)]
    def out(z,theta,vec): return (1-theta)*vec[z]+theta*vec[(z+1)%m]
    parts=[F(a,30) for a in range(31)]
    assert sum((out(z,F(0),f)+out(z,F(1),f)) for z in range(m))/(2*m)==sum(f)/m
    for shift in range(m):
        p=[f[(z-shift)%m] for z in range(m)]
        for z in range(m):
            for eta in parts:
                assert out(z,eta,p)==out((z-shift)%m,eta,f)
                shifts+=1

def sinc(x): return 1 if not x else sin(x)/x
def f(y,b): return 1+2*sum(b**(k*k)*cos(2*pi*k*y) for k in range(1,5))
def avg(y,b,m):
    return 1+2*sum(b**(k*k)*sinc(pi*k/m)*cos(2*pi*k*y) for k in range(1,5))

pairs=energy=0
for q in (3,5,7,9):
    for m in (q,2*q,7*q):
        for b in (.08,.04,.02):
            pay=[[avg((z+.5)/m-a/q,b,m)/m for z in range(m)] for a in range(q)]
            nu=[sum(pay[a][z] for a in range(q))/q for z in range(m)]
            for a in range(q):
                assert abs(sum(pay[a])-1)<1e-12
                shift=a*m//q
                assert max(abs(pay[a][z]-pay[0][(z-shift)%m]) for z in range(m))<1e-13
                Z=[log(pay[a][z]/nu[z]) for z in range(m)]
                mu=sum(p*v for p,v in zip(pay[a],Z))
                va=sum(p*(v-mu)**2 for p,v in zip(pay[a],Z))
                rh=sinc(pi/m)
                assert abs(mu-b*b*rh*rh)<15*b**3
                assert abs(va-2*b*b*rh*rh)<60*b**3
                for w in range(q):
                    A=sum(pay[a][z]*pay[w][z]/nu[z] for z in range(m))
                    assert abs(A-1-2*b*b*rh*rh*cos(2*pi*(a-w)/q))<20*b**4
                    pairs+=1

# Resolve the shape constant of positive linear interpolation by deterministic quadrature.
for b in (.025,.01):
    for m in (30,60,120,240):
        S=0.
        for z in range(m):
            l=(z+.5)/m
            fl,fr=avg(l,b,m),avg(l+1/m,b,m)
            for p in range(128):
                theta=(p+.5)/128
                fd=(1-theta)*fl+theta*fr
                S+=(f(l+theta/m,b)-fd)**2/fd
        v=S/(128*m)*m**4/b**2
        assert abs(v/(pi**4*49/90)-1)<.01
        energy+=1

windows=0
Phi=lambda t:(1+erf(t/sqrt(2)))/2
for t,gamma in ((.25,.5),(1,1),(1.8,3),(.7,.25)):
    # Shifted decision and reference interpolation windows have the proposed constants.
    D=t*pi*pi/(3*gamma**2)
    assert abs(Phi(D/(2*sqrt(2*t)))-Phi(-D/(2*sqrt(2*t)))
              -(2*Phi(pi*pi*sqrt(t)/(6*sqrt(2)*gamma**2))-1))<1e-13
    lam=F(49,90)*pi**4*t/gamma**4
    assert abs(sqrt(lam)/2-7*pi*pi*sqrt(t)/(6*sqrt(10)*gamma**2))<1e-13
    windows+=1

chords=0
for m in (3,5,15,50,200):
    rho=sinc(pi/m)
    for j in range(m):
        mid=(j+1)/m
        boundary=rho*cos(pi/m)
        assert max(rho*cos(2*pi*((z+.5)/m-mid)) for z in range(m)) <= boundary+1e-12
    for i in range(101):
        theta=i/100
        normal=cos(2*pi*(theta-.5)/m)-boundary
        approx=4*pi*pi/m**2*(1/24+theta*(1-theta)/2)
        assert normal>=0
        assert abs(normal-approx)<40/m**4
        chords+=1

print("PASS rational interpolation shifts / scalar grid moments / shape energies / window constants / chord bounds:",
      shifts,pairs,energy,windows,chords)
