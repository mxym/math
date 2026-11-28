#!/usr/bin/env python3
"""Exact synthetic checks for the ideal-direction alignment proof."""
from collections import Counter
from itertools import combinations_with_replacement, permutations, product


def conv(a, b):
    out = Counter()
    for x, u in a.items():
        for y, v in b.items():
            out[x+y] += u*v
    return out


def coeff_poly_exponent(values, d):
    atom = Counter(x*x for x in values)
    result = Counter({0: 1})
    for _ in range(d):
        result = conv(result, atom)
    return result


def field(d, p):
    z = next(t for t in range(1, p) if pow(t, d, p) == p - 1)
    w = [pow(z, j, p) for j in range(d)]
    assert len(set(w)) == d
    assert pow(z, 2*d, p) == 1
    assert not any((-a) % p in w for a in w)
    return w


def residue(word, w, p):
    return sum(a*b for a, b in zip(word, w)) % p


def orbit(d, p, w, support, vals):
    r = len(vals)
    survivors = 0
    if not any(a % p for a in vals):
        return 0
    mark = next(i for i, a in enumerate(vals) if a % p)
    coeffs = vals[:mark] + vals[mark+1:]
    c = vals[mark]
    labeled = 0
    for fixed in permutations(range(d), r-1):
        base = sum(a*w[j] for a, j in zip(coeffs, fixed))
        left = set(range(d)) - set(fixed)
        hits = sum((base+c*w[j]) % p == 0 for j in left)
        assert hits <= 1
        survivors += hits
        labeled += len(left)
    assert labeled == support
    assert survivors*(d-r+1) <= labeled
    return labeled


def test_deletion(d, p, bound, w):
    vals = range(-bound, bound+1)
    total, nonmultiple = Counter(), Counter()
    size = 0
    erased = set()
    for word in product(vals, repeat=d):
        e = sum(x*x for x in word)
        if not e or residue(word, w, p):
            continue
        assert e >= 3
        size += 1
        total[e] += 1
        marks = [i for i, x in enumerate(word) if x % p]
        if not marks:
            continue
        nonmultiple[e] += 1
        j = marks[0]
        c = word[j]
        beta = word[:j]+(0,)+word[j+1:]
        assert (beta, c) not in erased
        erased.add((beta, c))
        if abs(c) == 1:
            assert sum(x*x for x in beta) >= 2

    theta = coeff_poly_exponent(vals, d)
    # Coefficientwise finite analogue of the three terms in Eq. (6).
    rest = Counter({e:v for e,v in theta.items() if e >= 2})
    big = Counter(x*x for x in vals if abs(x) >= 2)
    multiples = coeff_poly_exponent([x for x in vals if x % p == 0], d)
    del multiples[0]
    rhs = conv(Counter({1:2}), rest) + conv(big, theta) + multiples
    assert all(v <= rhs[e] for e,v in total.items())
    assert sum(nonmultiple.values()) == len(erased)
    return (bound*2+1)**d, size


def test_fourier(d, p, w):
    # Synthetic, finite support: perm-invariant squared weights and rational
    # coordinate reset 1/5. Check the orbit L2 bound for every energy shell
    # by comparing exact integer numerators on a common denominator.
    from fractions import Fraction as F
    norm = Counter()
    effective = Counter()
    vals = (-1, 0, 1, p)
    reset = F(4, 5)
    for word in product(vals, repeat=d):
        if not any(x % p for x in word):
            continue
        r = sum(x != 0 for x in word)
        tag = (r, tuple(sorted(word)))
        norm[tag] += 1
        if not residue(word, w, p):
            effective[tag] += 1
    for tag, count in norm.items():
        r = tag[0]
        actual = F(effective[tag], count)*reset**(2*r)
        sharp = reset**(2*r)/F(d-r+1)
        coarse = F(2, d) if r <= d//2 else reset**d
        assert actual <= sharp
        assert actual <= coarse
    return len(norm)


def main():
    assigned = patterns = scanned = hits = tags = 0
    for d,p,max_r in ((2,5,2),(4,17,4),(8,17,4),(16,97,3)):
        w = field(d,p)
        coeffs = (-p, -2, -1, 1, 2, p)
        labeled = 1
        for r in range(1,max_r+1):
            labeled *= d-r+1
            for vals in combinations_with_replacement(coeffs, r):
                n = orbit(d,p,w,labeled,vals)
                if n:
                    assigned += n
                    patterns += 1
        if d <= 8:
            tags += test_fourier(d,p,w)
        if d <= 4:
            a,b = test_deletion(d,p,p+1,w) if d==2 else test_deletion(d,p,3,w)
            scanned += a
            hits += b
    print("PASS marked orbit patterns / labeled placements:", patterns, assigned)
    print("PASS exact deletion rows / residue hits:", scanned, hits)
    print("PASS Fourier occupation classes:", tags)


if __name__ == "__main__":
    main()
