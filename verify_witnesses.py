#!/usr/bin/env python3
"""Direct spectral witnesses; optionally check the complete Fuller catalogue."""
from collections import Counter
from hashlib import sha256
from math import isqrt
from pathlib import Path
from sys import argv
from zipfile import ZipFile
import re

CHAR = [sum(1 << x for x in range(64) if (a & x).bit_count() & 1)
        for a in range(64)]
EXPECTED = [
    {8:64}, {6:36,10:28}, {4:20,8:32,12:12}, {0:12,8:48,16:4},
]
CATALOGUE = "6f1d7c7012d987d2d75a9618dd569959e66928d573c5f9b43db0b4276bcdecf8"


def spec(f):
    return [abs(64-2*(f ^ a).bit_count()) for a in CHAR]


def punctured(w):
    return tuple(sorted(Counter(sorted(w)[1:]).items()))


def nth_root_integer(x, d):
    """Floor of x**(1/d), using only integer bisection."""
    lo, hi = 0, 1 << ((x.bit_length()+d-1)//d)
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**d<=x:
            lo=mid
        else:
            hi=mid
    return lo


def weights(n,d):
    # For each a, interval of width 2**(-70) containing a**(n/d).
    # If p = floor(2**70 * a**(n/d)), then p**d is bounded by
    # a**n * 2**(70*d); integers prove this exactly.
    factor=1 << (70*d)
    return {a:nth_root_integer(a**n*factor,d) for a in range(65)}


def catalogue(path, reps):
    assert sha256(path.read_bytes()).hexdigest()==CATALOGUE
    pat=re.compile(rb"class=\s*(\d+); tt=(0x[0-9A-F]{8}),(0x[0-9A-F]{8});")
    ids=set()
    profiles=set()
    with ZipFile(path) as z:
        assert len(z.namelist())==182
        for name in z.namelist():
            for line in z.read(name).splitlines():
                if not line.strip():
                    continue
                p=pat.fullmatch(line)
                assert p
                i=int(p[1])
                assert i not in ids
                ids.add(i)
                t=int(p[2],16)|(int(p[3],16)<<32)
                profiles.add(punctured(spec(t)))
    assert ids==set(range(1,150358)) and len(profiles)==2082
    assert set(reps)<=profiles
    for (n,d),w in zip(((1,1),(189,100),(191,100),(193,100)),reps):
        vv=weights(n,d)
        def val(h):
            return sum(vv[a]*c for a,c in h)
        best=val(w)
        assert all(best>val(z)+63 for z in profiles if z!=w), (n,d)
        print(f"Catalogue sanity: expected profile uniquely optimal at r={n}/{d}")
    assert max(sum(a*a*c for a,c in h) for h in profiles)==4096
    print("PASS: all 150357 IDs, 2082 spectra, exact rational-power sanity checks")


def main():
    b=sum(((((x & 3)==3)^((x & 12)==12)^((x & 48)==48))) << x for x in range(64))
    flips = [0,1,(1 << 0)|(1 << 1),sum(1 << j for j in (0,1,4,5))]
    reps=[]
    for name,change,expected,dc in zip("ABCD",flips,EXPECTED,(8,6,4,0)):
        f=b^change
        w=spec(f)
        assert Counter(w)==expected and w[0]==min(w)==dc
        assert sum(t*t for t in w)==4096
        reps.append(punctured(w))
        print(f"{name}: {f:016x}; unscaled full spectrum {dict(sorted(expected.items()))}; DC={dc}")
    assert Counter(spec(b^1)) != EXPECTED[0] # rejects a one-flip mutant of the bent witness
    if len(argv)==2:
        catalogue(Path(argv[1]),reps)
    else:
        assert len(argv)==1
    print("PASS: four direct witnesses and negative control")


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    main()
