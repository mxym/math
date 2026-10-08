#!/usr/bin/env python3
"""Independent exact arithmetic checker for the one-variable Schinzel-H reduction.

This verifies *only* a polynomial admissibility certificate; it DOES NOT
assert any integer input actually gives 197 primes. That conclusion is
explicitly conditional on Schinzel's unproved Hypothesis H.
"""
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

DIR=Path(__file__).resolve().parent
PATTERN=DIR.parents[1]/'sqrt-minus-two-universal-sieve-barrier'/'code'/'connected_shape.json'
PATTERN_SHA='b8036dcfa082e1329126041d8c7992139da6121e4ebf71599458619e7af93df0'


def demand(cond,msg):
    if not cond:raise ValueError(msg)


def prime(p):
    return type(p) is int and p>=2 and all(p%d for d in range(2,isqrt(p)+1))


def verify(data):
    demand(sha256(PATTERN.read_bytes()).hexdigest()==PATTERN_SHA,
           'original universally admissible shape changed')
    S=[tuple(z) for z in json.loads(PATTERN.read_text())]
    demand(len(S)==len(set(S))==197,'original shape not 197 distinct points')
    demand(set(data)=={'source_shape','number_of_forms','small_prime_cutoff',
                       'modulus','horizontal_offset','vertical_offset',
                       'prime_local_shifts'},'incorrect certificate fields')
    demand(data['number_of_forms']==len(S)==197 and
           data['small_prime_cutoff']==2*len(S)==394,
           'wrong polynomial family/threshold')
    raw_primes=[p for p in range(2,395) if prime(p)]
    shifts=data['prime_local_shifts']
    demand(type(shifts) is list and len(shifts)==len(raw_primes)==77,
           'missing or repeated small prime indices')
    demand([entry[0] for entry in shifts]==raw_primes,
           'small prime coverage/order invalid')
    M=int(data['modulus']);X=int(data['horizontal_offset']);Y=int(data['vertical_offset'])
    demand(0<=X<M and Y>=M and M>0,'noncanonical global CRT shift')
    computed_M=1
    for p,u,v in shifts:
        demand(type(u) is int and type(v) is int and 0<=u<p and 0<=v<p,
               'invalid local modular shift')
        computed_M*=p
        demand(X%p==u and Y%p==v,'CRT compatibility incorrect')
        for a,b in S:
            demand(((X+a)**2+2*(Y+b)**2)%p!=0,
                   f'polynomial product has forbidden divisor p={p} at n=0')
    demand(M==computed_M,'CRT modulus is not exactly product of all 77 primes')
    demand(all(Y+b>0 for a,b in S),'quadratic polynomial not irreducible')

    # Each f_z(T) = T^2+2(X+a)T+(X+a)^2+2(Y+b)^2 has positive monic
    # leading coefficient and negative discriminant -8(Y+b)^2.
    coeff=[(2*(X+a),(X+a)**2+2*(Y+b)**2) for a,b in S]
    demand(len(set(coeff))==197,'quadratic forms are not distinct')
    for (_,b), (linear,constant) in zip(S,coeff):
        discriminant=linear*linear-4*constant
        demand(discriminant==-8*(Y+b)**2 and discriminant<0,
               'nonirreducible or nonpositive quadratic form')

    # For every p>394, the 197 monic quadratics have product of
    # degree EXACTLY 394 over F_p, hence cannot vanish on all F_p.
    # This argument is a written finite-field root-count lemma, not
    # a purported enumeration of infinitely many primes.
    print('PATTERN: 197 independently pinned distinct lattice coordinates')
    print('FAMILY: 197 distinct monic integral quadratics with strictly negative discriminants')
    print('SMALL-PRIME LOCAL DATA: all 77 primes <=394 covered by one CRT shift at n=0')
    print('GLOBAL CRT MODULUS: digits',len(str(M)),'horizontal/vertical shift digits',len(str(X)),len(str(Y)))
    print('LARGE-PRIME REASON: product monic degree 394, so no fixed divisor prime p>394')
    print('SCHINZEL INPUTS EXACTLY VERIFIED; NO PRIMALITY EXISTENCE ASSERTED')


if __name__=='__main__':
    verify(json.loads((DIR/'schinzel_affine_family.json').read_text()))
