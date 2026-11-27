#!/usr/bin/env python3
"""Relative trace identity over a formal characteristic-two polynomial ring."""
from itertools import product


def xor(items):
    out = set()
    for a in items:
        if a in out:
            out.remove(a)
        else:
            out.add(a)
    return out


def mul(*xs):
    return xor(tuple(sorted(sum(a, ()))) for a in product(*xs))


def var(c):
    return {(c,)}


s, t, u, w, v, p = map(var, ("s", "t", "u", "w", "v", "p"))
U = (u, w, u ^ w)
V = (v, p, v ^ p)


def main():
    x = [s ^ p for p in U]
    y = [t ^ p for p in V]
    left = set()
    broken = set()
    right = mul(t,t) ^ mul(s,t)
    for i in range(3):
        j, k = (i+1)%3, (i+2)%3
        yn = mul(y[i],y[j])
        common = yn ^ mul(y[i],x[i]) ^ mul(y[i],x[i],x[j])
        left ^= common ^ mul(y[i],x[i],x[k])
        broken ^= common ^ mul(y[i],x[j],x[k])
        right ^= mul(V[i],V[j]) ^ mul(V[i],U[i],U[i]) ^ mul(V[i],s ^ {()},U[i])
    assert left == right and len(right) > 2
    assert broken != right
    print(f"PASS: relative-trace identity with {len(right)} terms; exponent mutant rejected")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with Python -O.")
    main()
