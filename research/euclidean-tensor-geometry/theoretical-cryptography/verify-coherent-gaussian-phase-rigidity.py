#!/usr/bin/env python3
"""Synthetic parity and finite Gaussian measurement checks; no external inputs."""
from collections import defaultdict
from cmath import exp as cexp
from itertools import product
from math import cos, exp, pi, sqrt

exact_checks = 0
numeric_checks = 0


def exact(ok):
    assert ok
    global exact_checks
    exact_checks += 1


def numeric(ok):
    assert ok
    global numeric_checks
    numeric_checks += 1


def spectrum(A,B,c):
    groups = defaultdict(list)
    for j,k in product(range(-5,6),repeat=2):
        groups[j%2,k%2].append((A*j*j+2*c*j*k+B*k*k,j,k))
    return groups


for A in range(2,14):
    for B in range(A,17):
        for c in range(1,A//2+1):
            for p,w,v in [
                ((1,0), A, {(1,0),(-1,0)}),
                ((0,1), B, {(0,1),(0,-1)}),
                ((1,1), A+B-2*c, {(-1,1),(1,-1)}),
            ]:
                a = spectrum(A,B,c)[p]
                exact(min(e for e,j,k in a)==w and {(j,k) for e,j,k in a if e==w}==v)


def full(A,B,c,R,t,x,y,N=32):
    z0 = defaultdict(float)
    z1 = defaultdict(complex)
    for j,k in product(range(-N,N+1),repeat=2):
        sig = exp(-t*(A*j*j+2*c*j*k+B*k*k))
        b = j%R,k%R
        z0[b] += sig*sig
        z1[b] += sig*cexp(1j*(x*j+y*k)/R)
    u = {p:abs(a)**2 for p,a in z1.items()}
    return z0,u


def parts(A,B,c,R,t,x,y,N=27):
    tau = t*R*R/2
    by = defaultdict(float)
    for j,k in product(range(-N,N+1),repeat=2):
        val = exp(-tau*(A*j*j+2*c*j*k+B*k*k))*cos(x*j+y*k)
        by[j%2,k%2] += val
    out = defaultdict(float)
    for j,k in product(range(-N,N+1),repeat=2):
        for (a,b),v in by.items():
            J,K = j+R*a/2,k+R*b/2
            out[j%R,k%R] += v*exp(-2*t*(A*J*J+2*c*J*K+B*K*K))
    return out


for A,B,c in [(1,3,0),(2,3,1),(4,9,1),(2,2,1)]:
    for R in range(1,7):
        for t in [.13,.28,1.03]:
            x,y = (pi/2,pi/2) if c==0 else (.19*pi,-.61*pi)
            a,b = full(A,B,c,R,t,x,y)
            right = parts(A,B,c,R,t,x,y)
            numeric(max(abs(b[p]-right[p]) for p in b)<3e-12)
            if c==0:
                s,w=sum(a.values()),sum(b.values())
                numeric(sum(abs(a[p]/s-b[p]/w) for p in a)<8e-14)


def dominant(z):
    return max(sum(max(x,0.) for x in z),sum(max(-x,0.) for x in z))


lo = 1.
for i,j in product(range(121),repeat=2):
    x,y = 2*pi*i/120,2*pi*j/120
    u,v,w = cos(x),cos(y),cos(y-x)
    numeric(abs(u*u+v*v+w*w-2*u*v*w-1)<2e-15)
    numeric(max(abs(u),abs(v),abs(w))>=.5-2e-15)
    numeric(dominant([u,v,w])>=1/sqrt(2)-2e-15)
    lo = min(lo,dominant([u,v,w]))
numeric(abs(lo-1/sqrt(2))<2e-15)


def scaled_weights(A,B,c,x,y,tau):
    C = A+B-2*c
    out = []
    G = spectrum(A,B,c)
    for p in [(1,0),(0,1),(1,1)]:
        out.append(sum(exp(-tau*(i-C))*cos(j*x+k*y) for i,j,k in G[p]))
    return out
# In cases with exponentially shorter pairs, implement their proven exact
# zero contributions, rather than treating floating-point cos(pi/2) as zero.
def upper(A,B,c,x,y,tau,kind):
    if kind=='strict':
        return dominant([0.,0.,scaled_weights(A,B,c,x,y,tau)[2]])
    if kind=='tie':
        z = scaled_weights(A,B,c,x,y,tau)
        for p in [(1,0)]:
            C = A+B-2*c
            z[0] = sum(exp(-tau*(i-C))*cos(j*x+k*y)
                       for i,j,k in spectrum(A,B,c)[p] if k)
        return dominant(z)
    return dominant(scaled_weights(A,B,c,x,y,tau))


for A,B,c,x,y,k,C in [
    (4,5,1,pi/2,pi/2,'strict',2),
    (2,5,1,pi/2,-pi/4,'tie',sqrt(2)),
    (2,2,1,pi/4,-pi/2,'equal',sqrt(2)),
]:
    for tau in [6,8,10]:
        numeric(abs(upper(A,B,c,x,y,tau,k)-C)<2e-9)

print(f'PASS: {exact_checks} exact parity assertions, {numeric_checks} floating checks')
