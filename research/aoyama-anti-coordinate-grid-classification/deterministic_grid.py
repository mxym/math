#!/usr/bin/env python3
"""Construct an anti-coordinate grid from arbitrary affine-plane line labels."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import comb, lcm, prod
import argparse
import json

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

SMALL = {
    4: [7,11,12,4,13,6,9,8,10,3,15,1,14,2,0,5],
    5: [13,0,3,24,17,8,15,14,10,12,21,18,9,16,23,19,6,11,2,1,7,22,5,4,20],
    7: [24,47,29,31,17,6,35,43,5,33,36,28,2,12,38,13,45,21,0,18,42,46,4,11,41,
        10,23,27,26,37,48,44,9,8,34,25,14,30,3,1,32,40,16,20,19,7,22,39,15],
}


def validate(D):
    n = len(D)-1
    N = n*n
    if n < 2 or any(Counter(row) != {i:n for i in range(n)} for row in D):
        raise ValueError("Each of n+1 direction rows must encode n lines of size n.")
    if not all(len(set(zip(a,b))) == N for a,b in combinations(D,2)):
        raise ValueError("Distinct classes must intersect once per line pair.")
    return n


def grid_blocks(n):
    for i in range(n):
        yield tuple(i*n+j for j in range(n))
    for j in range(n):
        yield tuple(i*n+j for i in range(n))


def is_anti(D,T):
    n = len(D)-1
    return (len(T)==n*n and set(T)==set(range(n*n)) and
            all(len({row[T[i]] for i in b})<n for b in grid_blocks(n) for row in D))


def conditional_grid(D):
    """D[d][p] is the line label of point p in direction d."""
    n = validate(D)
    if n < 8:
        raise ValueError("This derandomization starts from the union bound for n >= 8.")
    N = n*n
    blocks = list(grid_blocks(n))
    remaining = list(range(N))
    T = []
    available = [[n]*n for _ in D]
    directions = set(range(n))
    potential = Fraction(2*n*(n+1)*n**n,comb(N,n))
    if potential >= 1:
        raise ValueError("Initial first-moment bound failed.")

    for place in range(N):
        s = len(remaining)
        ev = []
        needed = set()
        for b in blocks:
            target = place in b
            used = [T[i] for i in b if i < place]
            r = n-len(used)-target
            needed.add(r)
            for d,a in enumerate(D):
                present = {a[x] for x in used}
                if len(present) != len(used):
                    continue
                missing = directions-present
                raw = prod(available[d][line] for line in missing)
                if raw:
                    ev.append((d,missing,raw,target,r))
        denominators = {r:comb(s-1,r) for r in needed}
        common = lcm(*denominators.values())
        mult = {r:common//denominators[r] for r in needed}

        vals = []
        for v in remaining:
            numerator = 0
            for d,missing,raw,target,r in ev:
                i = D[d][v]
                new = raw
                if i in missing:
                    count = available[d][i]
                    new = raw//count
                    if not target:
                        new *= count-1
                elif target:
                    new = 0
                numerator += mult[r]*new
            vals.append((numerator,v))
        # Independently check the conditional-expectation averaging identity.
        assert Fraction(sum(value for value,_ in vals),common*s)==potential
        value,v = min(vals)
        new_potential = Fraction(value,common)
        assert new_potential <= potential
        potential = new_potential
        remaining.remove(v)
        T.append(v)
        for d,a in enumerate(D):
            available[d][a[v]]-=1

    assert potential == 0 and is_anti(D,T)
    return T


def binary_mult(x,y,poly):
    limit=1<<(poly.bit_length()-1)
    z=0
    while y:
        if y&1:
            z^=x
        x<<=1
        if x&limit:
            x^=poly
        y>>=1
    return z


def field_plane(n):
    if n in (4,8):
        poly={4:7,8:11}[n]
        diff=lambda a,b:a^b
        mul=lambda a,b:binary_mult(a,b,poly)
    elif n==9:
        diff=lambda a,b:(a%3-b%3)%3+3*((a//3-b//3)%3)
        def mul(a,b):
            x,y=a%3,a//3
            u,v=b%3,b//3
            return (x*u-y*v)%3+3*((x*v+y*u)%3)
    else:
        diff=lambda a,b:(a-b)%n
        mul=lambda a,b:(a*b)%n
    return [[diff(y,mul(t,x)) for x,y in product(range(n),repeat=2)] for t in range(n)]+[
        [x for x,y in product(range(n),repeat=2)]]


def derived_order9():
    # In F9^2 replace the four F3-slope subspaces (including infinity) by
    # Z x Z for all four one-dimensional F3-subspaces Z of F9.
    n=9
    def add(a,b):
        return (a%3+b%3)%3+3*((a//3+b//3)%3)
    def times2(a):
        return add(a,a)
    candidates = sorted({tuple(sorted((0,a,times2(a)))) for a in range(1,n)})
    D=field_plane(n)[3:9]
    for Z in candidates:
        classes = sorted({tuple(sorted(add(x,z)*n+add(y,w) for z,w in product(Z,repeat=2)))
                          for x,y in product(range(n),repeat=2)})
        assert len(classes)==n
        a=[-1]*(n*n)
        for i,L in enumerate(classes):
            for j in L:
                assert a[j] == -1
                a[j]=i
        D.append(a)
    assert validate(D)==9
    return D


def digest(T):
    return sha256(json.dumps(T,separators=(",",":")).encode()).hexdigest()


def checks():
    for n,T in SMALL.items():
        D=field_plane(n)
        assert validate(D)==n and is_anti(D,T)
        assert not is_anti(D,list(range(n*n)))  # geometric directions are bad coordinates
        print(f"field order {n}, small witness {digest(T)}")
    for label,D in [(f"field order {n}",field_plane(n)) for n in (8,9,11)]+[
        ("derived-spread order 9",derived_order9())]:
        T=conditional_grid(D)
        print(f"{label}, deterministic {digest(T)}")
    try:
        bad=field_plane(8)
        bad[1]=bad[0]
        validate(bad)
    except ValueError:
        pass
    else:
        raise AssertionError("duplicate direction not rejected")
    print("PASS deterministic construction and controls")


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--input",help="JSON containing n+1 direction rows of n^2 line labels")
    args=parser.parse_args()
    if args.input:
        with open(args.input) as stream:
            D=json.load(stream)
        print(json.dumps(conditional_grid(D)))
    else:
        checks()
