#!/usr/bin/env python3
"""Exact integer Rayleigh certificate. No floating-point or third-party packages.

For the linear-first Gram convention, w* C(A) w is the squared norm of
sum_i conjugate(w_i) v_i tensor product_(j!=i) ell_j.
This finite certificate illustrates the theorem; it does not prove unboundedness.
"""

if not __debug__:
    raise SystemExit('Run without -O, -OO, or PYTHONOPTIMIZE: assertions are required for verification.')

import csv,json,math,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conjugate(a):return a[0],-a[1]
def abs2(a):return a[0]*a[0]+a[1]*a[1]
def poly_times_linear(p,v):
    q=[(0,0)]*(len(p)+1)
    for k,c in enumerate(p):
        q[k]=add(q[k],mul(c,v[0]));q[k+1]=add(q[k+1],mul(c,v[1]))
    return q
def product(v,omit=None):
    p=[(1,0)]
    for i,row in enumerate(v):
        if i!=omit:p=poly_times_linear(p,row)
    return p
def norm(p):
    d=len(p)-1
    return sum(math.factorial(k)*math.factorial(d-k)*abs2(c) for k,c in enumerate(p))
def verify():
    source=ROOT/'witness_n200.csv'
    raw=list(csv.reader(source.open(newline='')))
    assert raw[0]==['a_real','a_imag','b_real','b_imag','w_real','w_imag']
    rows=[list(map(int,row)) for row in raw[1:]]
    v=[((a,b),(c,d)) for a,b,c,d,e,f in rows];w=[(e,f) for a,b,c,d,e,f in rows]
    n=len(v);assert n==200
    assert all(abs2(a)+abs2(b)>0 for a,b in v)
    # A nonzero 2 by 2 minor proves exact rank two of the Gram factor.
    minor=add(mul(v[0][0],v[1][1]),tuple(-x for x in mul(v[0][1],v[1][0])))
    assert abs2(minor)>0
    P=product(v);permanent=norm(P);assert permanent>0
    G=[[(0,0)]*n for _ in range(2)];E=[[(0,0)]*n for _ in range(2)]
    for i,row in enumerate(v):
        q=product(v,i)
        for a in range(2):
            weight=mul(conjugate(w[i]),row[a])
            for k,c in enumerate(q):
                G[a][k]=add(G[a][k],mul(weight,c))
                E[a][k]=add(E[a][k],mul(row[a],c))
    rayleigh_numerator=sum(norm(p) for p in G)
    wnorm=sum(abs2(c) for c in w)
    denominator=permanent*wnorm
    # Independently check the all-ones row-sum / homogeneous-gradient identity.
    assert sum(norm(p) for p in E)==n*permanent
    assert 269*denominator < 100*rayleigh_numerator < 270*denominator
    result={'n':n,'rank':2,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'permanent':str(permanent),'w_norm_squared':str(wnorm),
            'w_star_Cw':str(rayleigh_numerator),'permanent_times_w_norm_squared':str(denominator),
            'strict_lower_gap_100_rayleigh_minus_269_denominator':str(100*rayleigh_numerator-269*denominator),
            'certified_rayleigh_interval':'269/100 < w* C(A) w / (per(A) ||w||^2) < 27/10',
            'all_ones_identity_verified':True,'arithmetic':'Python integers only'}
    (ROOT/'EXACT_WITNESS_RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('permanent','w_star_Cw','permanent_times_w_norm_squared','strict_lower_gap_100_rayleigh_minus_269_denominator')},indent=2))
if __name__=='__main__':verify()
