"""Exhaustive translation-reduced clique and projection comparison."""

from collections import defaultdict
from itertools import combinations, product
from math import gcd, isqrt

POS = tuple(range(4))
PAIRS = tuple(combinations(POS, 2))
TRIPLES = tuple(combinations(POS, 3))


def gram(a, b):
    return (sum(x*x for x in a), sum(x*y for x, y in zip(a, b)),
            sum(y*y for y in b))


def shells(L, T):
    cube = tuple(product(range(-T, T+1), repeat=L))
    targets = {gram(a, b) for a, b in product(cube, repeat=2)}
    H = isqrt(L*T*T)
    vv = tuple(product(range(-H, H+1), repeat=L))
    all_levels = defaultdict(list)
    for a, b in product(vv, repeat=2):
        g = gram(a, b)
        if g in targets:
            all_levels[g].append((a, b))
    assert all_levels.keys() == targets
    return all_levels


def dif(a, b, i, j, p):
    return tuple(((j-i)*x + (j*j-i*i)*y) % p for x, y in zip(a, b))


def minus(a, b, p):
    return tuple((x-y) % p for x, y in zip(a, b))


def reduced(F, p, indices):
    i = indices[0]
    return {tuple(dif(a, b, i, j, p) for j in indices[1:]) for a, b in F}


def edges(F, p):
    return {(i, j): {dif(a, b, i, j, p) for a, b in F} for i, j in PAIRS}


def cliques(E, p, indices):
    i, j, k = indices[:3]
    compatible = {(u, v) for u, v in product(E[i, j], E[i, k])
                  if minus(v, u, p) in E[j, k]}
    if len(indices) == 3:
        return compatible
    l = indices[3]
    return {(u, v, w) for u, v in compatible for w in E[i, l]
            if minus(w, u, p) in E[j, l] and minus(w, v, p) in E[k, l]}


def exhaustive():
    for i, j, k in TRIPLES:
        assert gcd(k-j, k-i) == 1
    for L, T, p in ((1, 3, 113), (2, 4, 223), (3, 1, 73)):
        levels = shells(L, T)
        all_count = tri_count = 0
        phase_boundary = False
        for g, F in sorted(levels.items()):
            E = edges(F, p)
            for I in TRIPLES + (POS,):
                expected = reduced(F, p, I)
                assert len(expected) == len(F)
                assert cliques(E, p, I) == expected
                if len(I) == 3:
                    tri_count += len(expected)
                else:
                    all_count += len(expected)
            phase_boundary |= any(abs(z) > T for pair in F for vec in pair for z in vec)
        if (L, T) == (2, 4):
            # Both pairs belong to the same level; the second is
            # outside the counting box and still belongs to the code.
            assert phase_boundary
            assert ((3, 4), (0, 0)) in levels[25, 0, 0]
            assert ((5, 0), (0, 0)) in levels[25, 0, 0]
        print(f"L={L}, T={T}, P={p}: {len(levels)} Gram levels, "
              f"{tri_count} normalized triangles, {all_count} normalized 4-cliques PASS")


def negative_controls():
    mixed = [((a,), (b,)) for a, b in product(range(-1, 2), repeat=2)]
    actual = cliques(edges(mixed, 101), 101, (0, 1, 2))
    projected = reduced(mixed, 101, (0, 1, 2))
    assert ((0,), (97,)) in actual - projected
    shell = [(a, a) for a in product(range(-2, 3), repeat=2) if sum(x*x for x in a) == 5]
    assert len(shell) == 8 and {gram(a, b) for a, b in shell} == {(5, 5, 5)}
    actual = cliques(edges(shell, 5), 5, (0, 1, 2))
    projected = reduced(shell, 5, (0, 1, 2))
    assert ((2, 4), (4, 3)) in actual - projected
    print("Negative controls: mixed Gram at P=101 and modular wrap at P=5 each create a spurious triangle")


def count_certificate():
    # An explicit T makes the pigeonhole lower bound exceed q even
    # at the maximum Bertrand prime cap. This is not a search for G.
    L = 8
    T = 100_000_000_000
    H = isqrt(L*T*T-1)+1
    assert (2*T+1)**(2*L) > 12*L**3*T**6 * (72*H)**L
    print(f"Pigeonhole integer certificate: L={L}, T={T}, H={H} forces |C|>q^2")


if __name__ == "__main__":
    exhaustive()
    negative_controls()
    count_certificate()
