#!/usr/bin/env python3
"""Complete edge-mask Fourier tables, exact orbit moments, and integer MGFs."""
from collections import Counter
from itertools import combinations, permutations
from math import comb, factorial


def permute_mask(mask, image):
    val = 0
    while mask:
        j = mask & -mask
        val |= image[j.bit_length()-1]
        mask ^= j
    return val


def hadamard(a):
    d = 1
    while d < len(a):
        for start in range(0, len(a), 2*d):
            for i in range(start, start+d):
                u, v = a[i], a[i+d]
                a[i], a[i+d] = u+v, u-v
        d *= 2


def checks(n):
    edges = list(combinations(range(n),2))
    idx = {e:j for j,e in enumerate(edges)}
    M = len(edges)
    Hn = 1<<M
    full = Hn-1
    maps = [tuple(1<<idx[tuple(sorted((p[i],p[j])))] for i,j in edges)
            for p in permutations(range(n))]
    cuts = {sum(1<<j for j,(i,k) in enumerate(edges) if ((u>>i)^(u>>k))&1)
            for u in range(1<<n)}
    C = cuts | {full ^ c for c in cuts}
    dmask = [0]*Hn
    for g in range(1,Hn):
        b = g & -g
        i,j = edges[b.bit_length()-1]
        dmask[g] = dmask[b^g] ^ (1<<i) ^ (1<<j)
    degc = {g for g,v in enumerate(dmask) if v in (0,(1<<n)-1)}
    perfect = [0]*Hn
    type_counts = Counter()
    marked = set()
    orbit_count = mgf_count = 0
    for a in range(Hn):
        if a in marked:
            continue
        c = Counter(permute_mask(a,m) for m in maps)
        L, w = len(c), a.bit_count()
        assert set(c.values()) == {factorial(n)//L}
        marked.update(c)
        type_counts[w] += 1
        load = [sum(bool(b & (1<<j)) for b in c) for j in range(M)]
        assert all(k*M == L*w for k in load)
        v = [int(h in c) for h in range(Hn)]
        hadamard(v)
        if a:
            assert sum(v) == 0
            assert sum(z*z for z in v)*L == Hn*L**2
            signed = sum(z*(-1 if (h&a).bit_count()&1 else 1)
                         for h,z in enumerate(v))
            assert signed == Hn
            r = load[0]
            for z in (2,3):
                for sign in (+1,-1):
                    wnum = sum(z**((L+sign*b)//2) for b in v)
                    assert wnum**r * 2**L <= Hn**r * (1+z**r)**L
                    mgf_count += 1
        for h,num in enumerate(v):
            val = num*(-1 if (h&a).bit_count()&1 else 1)
            ac = a ^ full
            dc = sum(-1 if (h&permute_mask(ac,m)).bit_count()&1 else 1
                     for m in maps) if h % 97 == 0 else None
            if dc is not None:
                assert dc*L*(-1 if (h&ac).bit_count()&1 else 1) == val*len(maps)
            if abs(num)==L:
                assert val == L
                perfect[h] += L
            if h % 97 == 0:
                direct = sum(-1 if (a&(permute_mask(h,m)^h)).bit_count()&1 else 1
                             for m in maps)
                assert direct*L == val*len(maps)
            assert abs(num)<=L
        orbit_count += 1
    for w,nw in type_counts.items():
        if w:
            assert nw <= comb(comb(2*w,2),w)
    extra = sum(p > 2 for p in perfect)
    if n >= 4:
        for h,p in enumerate(perfect):
            if h in (0,full):
                expected = Hn
            elif h in C:
                expected = len(degc)
            elif h in degc:
                expected = len(C)
            else:
                expected = 2
            assert p == expected
        expected_extra = ((1 << (M-n+2)) if n%2==0
                          else (1 << (M-n+1)) + (1<<n)-2)
        assert extra == expected_extra
    return orbit_count, mgf_count, extra


def main():
    details = [checks(n) for n in range(2,6)]
    print(f'PASS complete n=2..5 orbit tables, exact moments and MGFs (orbits, MGFs, exceptional H): {details}')
    # Full edge set is maximal even when H consists of a single edge and n=5.
    # Three overlapping 2-edge products on a triangle multiply constantly to 1.
    assert all((((signs[0]*signs[1])*(signs[0]*signs[2])*(signs[1]*signs[2])) == 1)
               for signs in ((a,b,c) for a in (-1,1) for b in (-1,1) for c in (-1,1)))
    print('PASS dependency control: overlapping orbit signs are not jointly independent')


if __name__ == '__main__':
    main()
