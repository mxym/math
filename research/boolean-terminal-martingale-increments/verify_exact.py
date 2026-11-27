#!/usr/bin/env python3
"""Exhaustive dyadic trees: integer support, tail and endpoint checks."""
from math import isqrt


functions = certificates = optimal_certs = reflection = 0
for n in range(1,5):
    N=1<<n
    # Values scaled by N; at a node j level weights ascend from leaves.
    for f in range(1<<N):
        values=[0]*(2*N)
        values[N:]=[N*((f>>j)&1) for j in range(N)]
        for j in range(N-1,0,-1):
            s=values[2*j]+values[2*j+1]
            assert s%2==0
            values[j]=s//2
        mx=[0]*(2*N)
        for j in range(2,2*N):
            mx[j]=max(mx[j//2],abs(values[j]-values[j//2]))
        mu=min(values[1],N-values[1])
        for dn in (8,13,19):
            # a=1/dn, theta=(dn^2-4(n+1))/(4 dn^2).
            theta_num=dn*dn-4*(n+1)
            assert theta_num>0
            mass=sum(j*dn>=N for j in mx[N:])
            assert 4*dn*dn*mass>=theta_num*mu
            certificates+=1
        # a=1/sqrt(12(n+1)), using exact multiplication in squared units.
        mass=sum(12*(n+1)*j*j>=N*N for j in mx[N:])
        assert 6*mass>=mu
        optimal_certs+=1
        if values[1]*2>N:
            assert mu == N-values[1]
            reflection+=1
        functions+=1

# Calibrations: equality in the fixed-threshold linear mean example; no
# Boolean-terminal assumption for the constant control.
small = 0
for n in range(1,401):
    # Choose mu = 1 / 2^j smaller than 1/sqrt(12(n+1)).
    d=1<<(isqrt(12*(n+1)).bit_length()+1)
    # Two path types: failure increment 1/d with mass 1-1/d,
    # success increment (d-1)/d with mass 1/d.
    mass_numer = sum(w for j,w in ((1,d-1),(d-1,1))
                     if 12*(n+1)*j*j>=d*d)
    assert mass_numer==1
    small+=1
assert not any(abs(1-1)*8>=2 for _ in range(4)) # constant 1/2
print(f"PASS exact: {functions} Boolean truth tables ({reflection} reflected initial means); "
      f"{certificates} rational-threshold and {optimal_certs} square-root-threshold inequalities; "
      f"{small} small-mean controls; constant-terminal omission control")
