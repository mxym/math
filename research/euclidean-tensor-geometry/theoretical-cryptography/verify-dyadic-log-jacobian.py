#!/usr/bin/env python3
"""Toy arithmetic checks for the dyadic log-Jacobian theorem."""
from math import gcd, pi, prod
import mpmath as mp
import numpy as np
import sympy as sp


def canonical_reduced_power_sum(n,q):
    """Power-basis coefficients of sum_{j<n} zeta^(q*j)."""
    a=[0]*n
    for j in range(n):
        t=q*j % (2*n)
        a[t%n]+=1 if t<n else -1
    return a


def negacyclic_matrix(a):
    n=len(a)
    M=np.zeros((n,n),dtype=np.int64)
    for j in range(n):
        for i,v in enumerate(a):
            k=(i+j)%n
            M[k,j]=v if i+j<n else -v
    return M


perms=orth=0
for n in (2,4,8,16,32,64,128,256):
    bs=range(1,n,2)
    for b in range(1,2*n,2):
        assert gcd(b,n)==1
        assert sorted(b*j%n for j in range(n))==list(range(n))
        assert not any(canonical_reduced_power_sum(n,2*b))
        perms+=1
    for b in bs:
        for c in bs:
            if b!=c:
                assert not any(canonical_reduced_power_sum(n,b+c))
                assert not any(canonical_reduced_power_sum(n,b-c))
                orth+=2

x=sp.Symbol("x")
rng=np.random.default_rng(91203627)
norm_checks=gram_checks=0
for n in (2,4,8,16):
    z=np.exp(1j*pi*np.arange(1,n,2)/n)
    for _ in range(16):
        a=[int(v) for v in rng.integers(-3,4,n)]
        if not any(a):
            a[0]=1
        q=sum(v*x**i for i,v in enumerate(a))
        norm=abs(int(sp.resultant(x**n+1,q,x)))
        assert norm>0
        B=negacyclic_matrix(a)
        assert abs(int(sp.Matrix(B.tolist()).det()))==norm
        logpro=2*sum(np.log(abs(np.polynomial.polynomial.polyval(z,a))))
        assert abs(logpro-np.log(norm))<1e-9
        norm_checks+=1
    for r,m in [(1,1),(1,3),(2,2),(2,3),(3,4)]:
        for _ in range(8):
            cs=rng.integers(-3,4,(r,m,n))
            A=np.block([[negacyclic_matrix(cs[i,j]) for j in range(m)]
                        for i in range(r)]).astype(float)
            ss=np.linalg.svd(A,compute_uv=False)
            if np.min(ss)<1e-10: # genuine rank deficiency possible in a toy draw
                continue
            log_J=sum(np.log(ss))
            blocks=np.stack([sum(cs[:,:,k]*zz**k for k in range(n)) for zz in z])
            log_J_embed=0
            for block in blocks:
                log_J_embed+=2*sum(np.log(np.linalg.svd(block,compute_uv=False)))
            assert abs(log_J-log_J_embed)<5e-8
            gram_checks+=1

angle_checks=0
for n in (16,32,64,256,1024,4096,16384):
    base=pi*np.arange(n)/n
    for phase in np.linspace(-1.1,1.1,21):
        cs=np.cos(base-phase)
        for amp in (0.,.001,.2,.5):
            x0=amp*cs
            assert abs(np.mean((x0-np.rint(x0))**2)-amp*amp/2)<1e-12
            angle_checks+=1
        # Numerical corroboration on an interval larger than the conservative
        # Riemann-proof cutoff; the proof supplies the unconditional bound.
        for amp in np.linspace(.51,max(.51,.001*n),25):
            x0=amp*cs
            assert np.mean((x0-np.rint(x0))**2) > .01
            angle_checks+=1

mp.mp.dps=80
chars=0
for t in (mp.mpf("0.28"),mp.mpf("0.4"),mp.mpf("0.6"),1,2,5,20):
    K=int(32+14*t)
    w=[mp.exp(-mp.pi*(mp.mpf(j)/t)**2) for j in range(1,K+1)]
    z=1+2*sum(w)
    v=2*sum(j*j*p for j,p in enumerate(w,1))/z
    for jj in range(1,51):
        a=mp.mpf(jj)/100
        direct=(1+2*sum(p*mp.cos(2*mp.pi*j*a) for j,p in enumerate(w,1)))/z
        assert abs(direct)<=mp.exp(-v*a*a/20)+mp.mpf("1e-70")
        chars+=1

print("PASS exact dyadic permutations",perms,"mixed orthogonality sums",orth)
print("PASS exact norm cases",norm_checks,"real/complex Jacobian cases",gram_checks)
print("PASS angular grid comparisons",angle_checks,"scalar characteristic comparisons",chars)
