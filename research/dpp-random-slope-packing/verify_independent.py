#!/usr/bin/env python3
"""Direction, packing-budget and decoder tests independent of main enumeration."""
from fractions import Fraction
from itertools import combinations, product
from math import gcd
import random
import runpy
from pathlib import Path

# Use published decoder only as system under test; reference is modular
# inversion of the other coordinate or a separately obtained value.
sut = runpy.run_path(str(Path(__file__).with_name("verify_exact.py")))
count, unique = sut["count"], sut["unique"]


def by_x(p,t,z,alo,ahi,blo,bhi):
    if t == 0:
        return [(a,b) for a in range(alo,ahi+1) if a%p==z
                for b in range(blo,bhi+1)]
    inv = pow(t,-1,p)
    result = []
    for a in range(alo,ahi+1):
        b = blo + ((z-a)*inv-blo) % p
        if b <= bhi:
            result.append((a,b))
    return result


def check_decoder():
    rng = random.Random(736019)
    sampled = big = 0
    for p in (7,11,29,101,257,1009,2**61-1,2**127-1):
        for i in range(400):
            alo = rng.randrange(-p,p)
            blo = rng.randrange(-p,p)
            ahi = alo+rng.randrange(0,min(p,29))
            bhi = blo+rng.randrange(0,min(p,39))
            t = 0 if i%19 == 0 else rng.randrange(1,p)
            a, b = rng.randrange(alo,ahi+1),rng.randrange(blo,bhi+1)
            z = (a+t*b) % p if i%2 else rng.randrange(p)
            solution = by_x(p,t,z,alo,ahi,blo,bhi)
            assert count(p,t,z,alo,ahi,blo,bhi) == len(solution)
            if len(solution) == 1:
                assert unique(p,t,z,alo,ahi,blo,bhi) == solution[0]
            sampled += 1
    # Large-box cases too large for either direct coordinate scan.
    p, b1, b2 = 2**127-1,2**33+9,2**37-1
    t = 2*b1+1
    for a,b in product((-b1,-1,0,1,b1),(-b2,-1,0,1,b2)):
        z = (a+t*b) % p
        assert unique(p,t,z,-b1,b1,-b2,b2) == (a,b)
        big += 1
    p, t, z = 2**127-1,1,0
    assert count(p,t,z,-b1,b1,-b2,b2) == 2*b1+1
    z = b1+b2+1
    assert count(p,t,z,-b1,b1,-b2,b2) == 0
    print(f"independent decoder: {sampled} translated boxes by inverse; "
          f"{big+2} large-box known values (127-bit field)")


def check_directions():
    checks = 0
    for p in (5,11,23,37,41,97):
        for b1,b2 in product(range(1,min(8,(p-1)//4)+1),repeat=2):
            rect = list(product(range(-b1,b1+1),range(-b2,b2+1)))
            directions = set()
            reduced = set()
            for x,y in combinations(rect,2):
                dx,dy = y[0]-x[0],y[1]-x[1]
                if dy:
                    directions.add((-dx*pow(dy,-1,p)) % p)
                    g = gcd(dx,dy)
                    dx,dy = dx//g,dy//g
                    if dy < 0:
                        dx,dy = -dx,-dy
                    reduced.add((dx,dy))
            norm = {(-dx*pow(dy,-1,p))%p
                    for dx in range(-2*b1,2*b1+1)
                    for dy in range(1,2*b2+1) if gcd(dx,dy)==1}
            assert directions == norm
            assert len(directions) <= len(reduced) <= (4*b1+1)*(4*b2+1)-1
            checks += 1
    print(f"independent bad-slope sets: {checks} pair-vs-primitive-direction comparisons")


def ceil(x):
    return -(-x.numerator//x.denominator)


def check_parameters():
    cases = 0
    for s,e,d in product((1,2,3,39,40,41,399,400,401,10**6,10**24),
                         (1,2,7,13,41,61,127,511),(0,1)):
        eps = Fraction(1+2*d,2**e)
        if not 0 < eps < 1:
            continue
        eta = eps/4
        target = ceil(16*(s+400)/eps)
        for p_axis in (target+1,2*target):
            # Test both monotone interval endpoints; these are integer
            # bounds, not evidence any particular endpoint is prime.
            ell = (p_axis-1).bit_length()
            for n in (0,s):
                mu = n+2*s*ell+400
                gamma = ceil(100*mu*p_axis/eta)
                ex = Fraction(mu*mu*gamma*p_axis*p_axis,1)/eta**2
                P = ceil(ex)
                b1,b2 = mu*(p_axis*gamma-1)//2,mu*(p_axis-1)//2
                assert p_axis >= 5 and Fraction(2*s+1,p_axis) <= eta
                assert Fraction(1,p_axis) <= eta and mu >= 400
                assert P > 4*max(b1,b2) and P > p_axis
                box = (2*b1+1)*(2*b2+1)
                dif = (4*b1+1)*(4*b2+1)-1
                assert box<=mu*mu*p_axis*p_axis*gamma
                assert dif+box <= 5*box
                assert Fraction(box,P)<=eta**2
                assert Fraction(101,100)*eta+(dif+box)/Fraction(P)<=eps
                assert Fraction(101,100)*eta+2*eta**2<=eps
                assert Fraction(101,100)*eta+10*eta**2<=eps
                assert P <= 101*mu**3*p_axis**3/eta**3+1
                cases += 1
    print(f"independent exact parameter arithmetic: {cases} cases (up to 511-bit error)")


if __name__ == "__main__":
    check_decoder()
    check_directions()
    check_parameters()
    print("PASS independent direction / decoder / parameter audit")
