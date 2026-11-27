#!/usr/bin/env python3
"""Verify the five homogeneous witnesses by exhaustive Boolean truth tables. Stdlib only."""
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit("Run without -O")
BASES = json.loads(Path(__file__).with_name("bases.json").read_text())
MOD = {2: 7, 3: 11, 4: 19, 5: 37, 6: 67}


def block(d, x):
    mask = 2**d - 1
    a, b, s = x & mask, (x >> d) & mask, (x >> (2*d)) & 1
    ab = b << 1
    if ab >> d:
        ab ^= MOD[d]
    return ((a & (ab ^ (b if s else 0))).bit_count() & 1), s


def f(n, z):
    u, s = block(2, z & 31)
    v, t = block((n-6)//2, z >> 5)
    return u ^ v ^ (s & t)


def tables(n, basis):
    assert len(basis) == n and all(0 < b < 1 << n for b in basis)
    perm, linear = [0], [0]
    for b in basis:
        perm += [x ^ b for x in perm]
        bit = f(n,b)
        linear += [x ^ bit for x in linear]
    assert len(set(perm)) == 1 << n
    return [f(n,z) ^ v for z,v in zip(perm,linear)]


def anf_and_walsh(values):
    an = values[:]
    wa = [1-2*x for x in values]
    step = 1
    while step < len(an):
        for start in range(0,len(an),2*step):
            for j in range(start,start+step):
                k = j+step
                an[k] ^= an[j]
                wa[j],wa[k] = wa[j]+wa[k],wa[j]-wa[k]
        step *= 2
    return an, wa


def form_rank(n, terms):
    cons = [0]*n
    for i in range(n):
        for mask in terms:
            if (mask >> i)&1:
                cons[i] ^= 1 << (mask ^ (1<<i))
    piv = {}
    for v in cons:
        while v:
            p = v.bit_length()
            if p not in piv:
                piv[p]=v
                break
            v ^= piv[p]
    return len(piv)


def digest(n,terms):
    return hashlib.sha256(b''.join(m.to_bytes(3,'little') for m in sorted(terms))).hexdigest()


if __name__ == '__main__':
    assert set(BASES) == {'10','12','14','16','18'}
    for n in range(10,19,2):
        v = tables(n,BASES[str(n)])
        a, w = anf_and_walsh(v)
        terms = [i for i,x in enumerate(a) if x]
        assert terms and {i.bit_count() for i in terms} == {3}
        assert set(w) == {1<<(n//2), -(1<<(n//2))}
        rank = form_rank(n, terms)
        assert rank==n
        print(f"n={n} cubic_terms={len(terms)} abs_W={abs(w[0])} contraction_rank={rank} ANF_SHA256={digest(n,terms)}")
    # A broken basis and a corrupted truth table must not pass.
    bad = BASES['10'][:]; bad[-1]=bad[0]
    try:
        tables(10,bad)
    except AssertionError:
        pass
    else:
        raise RuntimeError("duplicate-column negative control did not fail")
    v=tables(10,BASES['10']);v[-1]^=1
    a,w=anf_and_walsh(v)
    assert a[-1] and {abs(x) for x in w}!={32}
    print("PASS: exhaustive truth tables; duplicate-column and one-bit controls detected")
