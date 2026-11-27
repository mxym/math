#!/usr/bin/env python3
"""Separate character check, exact aggregate replay, and residual tables."""
from collections import Counter
from fractions import Fraction as R
from itertools import combinations, product
from math import factorial


def pascal_mult(a,b,poly):
    w = poly.bit_length()-1
    c = 0
    for i in range(w):
        c ^= (a<<i) if b>>i&1 else 0
    for j in range(2*w-2,w-1,-1):
        c ^= (poly<<(j-w)) if c>>j&1 else 0
    return c


def check_spectra():
    checked = 0
    for q,poly,ds in ((2,3,(1,2,3)), (4,7,(1,2))):
        w = q.bit_length()-1
        add = lambda x,y:x^y
        mul = lambda a,b:pascal_mult(a,b,poly)
        trace = lambda a:(a^mul(a,a)) if q==4 else a
        for d in ds:
            count = q**(2*d)
            coords = [tuple((i>>(w*j))&(q-1) for j in range(2*d))
                      for i in range(count)]
            qval = [0]*count
            for i,V in enumerate(coords):
                for j in range(d):
                    qval[i] ^= mul(V[j],V[j+d])
            Z = tuple(range(1,count)) if count<=64 else (1,q,1+q,q**d,count-1)
            for z in Z:
                linear = [qval[i]^qval[i^z]^qval[z] for i in range(count)]
                for s,t in product(range(q),repeat=2):
                    cf = sum(1-2*trace(add(mul(s,u),mul(t,v)))
                             for u,v in zip(qval,linear))
                    assert abs(cf)==(q**d if s else 0 if t else count)
                    checked += 1
    print(f'independent character proof: {checked} exact coefficient values')


def distribution(bits):
    """GF(2)^4 carriers, XOR input oracle with role-dependent offsets."""
    phase = tuple(((x & 1) & (x >> 2 & 1)) ^ ((x >> 1 & 1) & (x >> 3 & 1))
                  for x in range(16))
    out = Counter()
    for roles in product(range(3),repeat=len(bits)):
        count = sum(1<<(2*r) for r in roles)
        plain = sum(b^(r!=0) for b,r in zip(bits,roles))&1
        for vals in product(range(16),repeat=len(bits)):
            carrier = 0
            masked = plain
            for r,x in zip(roles,vals):
                carrier ^= x<<(4*r)
                masked ^= phase[x]
            out[count,carrier,masked] += 1
    return out


def verify_replay():
    cases = tuple(product((0,1),repeat=3))
    laws = {xs:distribution(xs) for xs in cases}
    good = sum(1<<(2*r) for r in range(3))
    compare = {}
    phase = lambda x: ((x & 1) & (x >> 2 & 1)) ^ ((x >> 1 & 1) & (x >> 3 & 1))
    max_bad_tv = R(0)
    for xs,law in laws.items():
        yes,no = Counter(),Counter()
        for (cnt,V,key),w in law.items():
            if cnt==good:
                decoded = key
                for r in range(3):
                    decoded ^= phase(V>>(4*r)&15)
                assert decoded==sum(xs)%2
                yes[cnt,V,key] += w
            else:
                no[cnt,V,key] += w
        assert sum(yes.values())==factorial(3)*16**3
        assert R(sum(yes.values()),sum(law.values()))==R(2,9)
        y = sum(xs)%2
        if y in compare:
            assert yes==compare[y]
        compare[y] = yes
        pairs = {(a,b) for a,b,_ in no}
        d = sum(abs(no[a,b,0]-no[a,b,1]) for a,b in pairs)
        tv = R(d,2*sum(no.values()))
        assert tv<=R(1,32)
        max_bad_tv=max(max_bad_tv,tv)
    assert distribution((0,1))==distribution((1,0))
    # At all-singleton occupied roles (e.g. 0 and 1), zero and two ones
    # have the same base-XOR residual: this toy inner family is used
    # only for the wrapper calculation, not as a separation example.
    assert distribution(())==Counter({(0,0,0):1})
    print(f'independent full-sum toy replay: 8 inputs x {3**3*16**3} equally likely '
          f'draws, good role probability 2/9, max bad-slot TV {max_bad_tv}, '
          'proper permutations exact')


def check_residuals_and_comparison():
    patterns = tuple(product((0,1),repeat=4))
    separated = []
    m = (0,0,1,1)
    checks = 0
    for word in patterns:
        ok = True
        for mask in range(7):
            H = tuple(i for i in range(3) if mask>>i&1)
            C = tuple(i for i in range(3) if not mask>>i&1)
            seen = {}
            for xs in product((0,1),repeat=len(H)):
                table = tuple(word[sum(xs)+sum(y)] for y in product((0,1),repeat=len(C)))
                if table in seen and seen[table] != sum(xs):
                    ok = False
                seen[table] = sum(xs)
                if word==m:
                    expect={0:{0:(0,0,0,1,0,1,1,1)},
                            1:{0:(0,0,0,1),1:(0,1,1,1)},
                            2:{0:(0,0),1:(0,1),2:(1,1)}}[len(H)][sum(xs)]
                    assert expect==table
                checks += 1
        if ok:
            separated.append(''.join(map(str,word)))
    assert len(separated)==8 and '0011' in separated
    # Exhaustively compare majority fibers for modular product on small moduli.
    trials = 0
    for q in range(2,9):
        for a0,a1,b0,b1,c0,c1 in product(range(q),repeat=6):
            lows = (a0*b0*c0%q,a1*b0*c0%q,a0*b1*c0%q,a0*b0*c1%q)
            highs = (a0*b1*c1%q,a1*b0*c1%q,a1*b1*c0%q,a1*b1*c1%q)
            assert not(len(set(lows))==len(set(highs))==1 and lows[0]!=highs[0])
            trials += 1
    print('symmetric 3-bit histogram-separating words:', ','.join(separated))
    print(f'independent residual tables: {checks} assignments incl. all majority3 '
          f'proper views; {trials} modular-product preprocessing checks')
    print('PASS independent spectral, aggregate, residual and comparison checks')


if __name__=='__main__':
    check_spectra()
    verify_replay()
    check_residuals_and_comparison()
