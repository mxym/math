#!/usr/bin/env python3
"""Exact trilinear ranks and low-pair iteration in finite algebraic models."""
from itertools import combinations, product
from fractions import Fraction as F


def span(basis):
    a = [0]
    for b in basis:
        a += [x ^ b for x in a]
    return frozenset(a)


def basis(seq):
    piv = {}
    for a in seq:
        while a:
            j = a.bit_length() - 1
            if j not in piv:
                piv[j] = a
                break
            a ^= piv[j]
    return tuple(piv.values())


def rank(seq):
    return len(basis(seq))


def tensor(terms):
    # A coordinate coefficient is a bit mask in the target vector space.
    def f(a, b, c):
        acc = 0
        for (i, j, k), value in terms:
            d = 0
            for u, v, w in ((i, j, k), (i, k, j), (j, i, k), (j, k, i), (k, i, j), (k, j, i)):
                d ^= ((a >> u) & (b >> v) & (c >> w)) & 1
            if d:
                acc ^= value
        return acc
    return f


def contraction(f, a, b, vs):
    return rank(f(a, b, v) for v in vs)


def fourfold(a):
    aa = {x ^ y for x in a for y in a}
    return {x ^ y for x in aa for y in aa}


def fourfold_core(v, a, n):
    # Elementary Fourier subspace, not a test of Sanders's asymptotic result.
    # Exact unnormalised character coefficient magnitude cut:
    # (coeff/|V|)^2 >= alpha^3/2.
    chi = []
    for h in range(1 << n):
        coeff = sum((-1)**((x & h).bit_count() % 2) for x in a)
        if 2*coeff*coeff*len(v) >= len(a)**3:
            chi.append(h)
    z = frozenset(x for x in v if all((x & h).bit_count() % 2 == 0 for h in chi))
    assert span(basis(z)) == z and z <= fourfold(a)
    return z


# Independent-output full monomial map: after restriction to a six-space,
# verify rank m-2 for every independent pair (a smaller finite model).
full = tensor([(t, 1 << i) for i, t in enumerate(combinations(range(6), 3))])
checks = 0
for a in range(1, 64):
    for b in range(1, 64):
        rr = contraction(full, a, b, [1 << j for j in range(6)])
        assert rr == (0 if a == b else 4)
        checks += 1
print(f"full cubic monomial contraction ranks: {checks} PASS")

# One dense but non-subspace low-rank row, realised in dimension 7.
# Against a=e_0 the maps b -> T(a,b,-) are contractions of the three disjoint
# pairs obtained from the three edge terms below. Rank is the number of
# nonzero pair blocks, so the set of rank strictly below 2 is not a subspace.
n = 7
rowf = tensor([((0, 1, 2), 1), ((0, 3, 4), 2), ((0, 5, 6), 4)])
v = frozenset(range(1 << n))
vr = [1 << j for j in range(n)]
row = {b for b in v if contraction(rowf, 1, b, vr) < 2}
assert len(row) == 20 and any(x ^ y not in row for x in row for y in row)
z = fourfold_core(v, row, n)
assert all(contraction(rowf, 1, b, vr) <= 4 for b in z)
print("non-subspace low-rank row and exact Fourier 4A core: PASS")

# Implement the induction at small dimension with a single-output cubic
# T=e_0 wedge e_1 wedge e_2 + e_3 wedge e_4 wedge e_5. Rank <2 for all pairs.
n = 8
lo = tensor([((0, 1, 2), 1), ((3, 4, 5), 1)])
v = frozenset(range(1 << n))
old = []
nontrivial = 0
for j in range(4):
    vb = basis(v)
    a = min(v - {0})
    r = 2
    row = {b for b in v if contraction(lo, a, b, vb) < r}
    vp = fourfold_core(v, row, n)
    nontrivial += sum(contraction(lo, i, a, vb) for i in old)
    h = a & -a  # A hyperplane test functional with value 1 at a.
    v = frozenset(x for x in vp if not (x & h) and all(lo(i, a, x) == 0 for i in old))
    old.append(a)
    u = span(old)
    assert len(u) == 1 << (j+1)
    assert u & v == {0}
    assert all(lo(i, k, b) == 0 for i, k, b in product(old, old, basis(v)))
    assert all(lo(i, k, b) == 0 for i, k, b in product(old, repeat=3))
    assert all(contraction(lo, i, x, basis(v)) <= 4*(r-1) for i, x in product(old, v))
assert nontrivial > 0 and lo(1, 2, 4) == 1  # Negative control: merely choose the first 3 axes.
print(f"dense-row induction: 4 steps; nonzero kernel ranks summed={nontrivial} PASS")

# Test the new even-convolution argument by comparing two exact methods:
# enumerate the sum multiplicities, and independently compute the spectrum.
n = 3
size = 1 << n
def char(u, v):
    return 1 if (u & v).bit_count() % 2 == 0 else -1

tested = sign_terms = 0
for mask in range(1, 1 << size):
    a = tuple(i for i in range(size) if mask & (1 << i))
    alpha = F(len(a), size)
    spectrum = [F(sum(char(u, x) for x in a), len(a)) for u in range(size)]
    assert sum(c*c for c in spectrum) == 1/alpha
    for theta, h in ((F(1, 2), 6), (F(1, 4), 4), (F(3, 4), 12)):
        assert theta**(h-2) < alpha
        large = tuple(u for u, c in enumerate(spectrum) if abs(c) >= theta)
        core = [x for x in range(size) if all(char(u,x) == 1 for u in large)]
        assert len(core) == 1 << (n-rank(large))
        assert rank(large) <= 2*(n-len(a).bit_length()+1)/theta**2
        coeff = [1]+[0]*(size-1)
        for _ in range(h):
            coeff = [sum(coeff[x ^ u] for u in a) for x in range(size)]
        for x in core:
            low = sum(c**h * char(u,x) for u,c in enumerate(spectrum) if u not in large)
            assert abs(low) <= theta**(h-2)/alpha < 1
            assert sum(spectrum[u]**h for u in large) >= 1
            sign_terms += sum(char(u,x) == -1 and c != 0 for u,c in enumerate(spectrum))
            assert F(size*coeff[x], len(a)**h) == low + sum(spectrum[u]**h for u in large)
            assert coeff[x] > 0
        tested += 1
assert sign_terms > 0
print(f"even convolution and large-spectrum subspace: {tested} exact cases PASS")
