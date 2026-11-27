#!/usr/bin/env python3
"""Independent finite checks of mixed-support constraints and counting."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product


def xor(seq):
    x = 0
    for y in seq:
        x ^= y
    return x


def span(basis):
    a = [0]
    for b in basis:
        a += [x ^ b for x in a]
    return set(a)


def make_basis(points):
    u = {0}
    b = []
    for x in sorted(points):
        if x not in u:
            b.append(x)
            u |= {v ^ x for v in u}
    assert u == set(points)
    return tuple(b)


def symplectic3(x, y, z):
    return xor(((x >> i) & (y >> j) & (z >> k) & 1)
               for i,j,k in permutations((0,1,2)))


# Use separately supported multilinear forms, including a non-alternating
# bilinear condition, and check every injection when a new direction enters.
N, d, m = 5, 3, 3
forms = [((i,), lambda a: a & 1) for i in range(d)]
forms.append(((0,1), lambda a,b: (a >> 1) & (b >> 1) & 1))


def legal(t):
    return all(phi(*(t[i] for i in ids)) == 0 for ids,phi in forms)


for x in product(range(1 << N),repeat=d):
    if legal(x):
        assert symplectic3(*x) == 0

B = []
used = 0
for j in range(m):
    kers = []
    for ids, phi in forms:
        for i in range(len(ids)):
            for v in permutations(B,len(ids)-1):
                kers.append((phi,i,v))
    for x in range(1 << N):
        if x not in span(B) and all(fn(*(t[:i]+(x,)+t[i:])) == 0 for fn,i,t in kers):
            B.append(x)
            break
    assert len(B) == j+1
    used += len(kers)
    for ids,phi in forms:
        assert all(phi(*t) == 0 for t in permutations(B,len(ids)))
assert B == [2,4,8]
assert not legal((2,2,4))  # Don't apply the defining constraint to repetitions.
assert symplectic3(2,2,4) == 0
assert not legal((2,6,8))  # Old pair breaks its form even with new vector outside its support.
assert all(x & 1 == 0 for x in (2,6,8))
assert all(symplectic3(*t) == 0 for t in product(span(B),repeat=d))
print(f"mixed-support greedy restriction: {used} constraints; repetitions negative control PASS")

# The Appendix 6.1 tree is checked by actual coordinate-sum closure,
# allowing the two branches to choose different intermediate coordinates.
def coordinate_sum(points, i):
    rows = defaultdict(set)
    for t in points:
        rows[t[:i]+t[i+1:]].add(t[i])
    return {r[:i]+(x^y,)+r[i:] for r,vals in rows.items() for x in vals for y in vals}

n, k, r = 4, 3, 2
P = {t for t in product(range(1 << n),repeat=k)
     if not (t[0]&1) and not ((t[1]>>1)&(t[2]>>2)&1)}
dropped = {(0,0,0)}
assert dropped <= P and len(dropped)*(1 << (2*k+k*r)) == 1 << (n*k)
S = P-dropped
for i in range(k):
    S = coordinate_sum(S,i)
assert S == P
assert coordinate_sum({(1,1)},0) != {(0,0),(1,1)}  # Arbitrary sets need not close to a variety.
print(f"sparse-deletion coordinate-sum tree: {len(P)} points PASS")

# Independently count collision incidence for a genuinely noninjective
# polynomial sampler with both good and bad cosets.
def cosets(W, n):
    return {tuple(sorted(x ^ v for v in W)) for x in range(1 << n)}

n = 4
planes = {tuple(sorted((0,a,b,a^b))) for a in range(1,16) for b in range(1,16) if a!=b}
assert len(planes) == 35
sampler = tuple((x>>1) + ((x&1)*(x>>1&1) << 3) for x in range(16))
entropy_inv = F(max(Counter(sampler).values()),16)
avg = F(0); positive = trials = 0
for V in planes:
    collisions = {x for C in cosets(V,n) for x in C
                  if any(y!=x and sampler[y]==sampler[x] for y in C)}
    avg += F(len(collisions),16*len(planes))
    for w in V[1:]:
        C = cosets({0,w},n)
        good = [cell for cell in C if len({sampler[x] for x in cell}) == 2]
        bad = len(C)-len(good)
        assert bad <= len(collisions)
        if good:
            xs = [x for cell in good for x in cell]
            A,B = Counter(sampler),Counter(sampler[x] for x in xs)
            tv = sum(abs(F(A[y],16)-F(B[y],len(xs))) for y in A)/2
            assert tv <= F(bad,len(C))
            positive += bad>0
        trials += 1
assert avg <= 4*entropy_inv and positive>0
print(f"noninjective input: {trials} coset refinements, {positive} nontrivial TV tests PASS")

# Alternating-form restriction uniformity: independent coefficient
# enumeration and direct additive differences on sampled hyperplanes.
def f_eval(x, masks, u):
    return xor((u >> i)&1 for i,a in enumerate(masks) if x&a == a)


def polar(x, masks, u):
    return xor(f_eval(z,masks,u) for z in span(x))

spaces = [{x for x in range(16) if (x&i).bit_count()%2 == 0} for i in range(1,16)]
checks = 0
for degree in (2,3):
    masks = tuple(i for i in range(16) if i.bit_count()==degree)
    for H in spaces:
        b = make_basis(H)
        coeffs = Counter(tuple(polar(t,masks,u) for t in combinations(b,degree))
                         for u in range(1 << len(masks)))
        assert len(coeffs) == 1 << len(tuple(combinations(b,degree)))
        assert len(set(coeffs.values())) == 1
        checks += 1
print(f"sharpness-model restriction surjectivity: {checks} exact distributions PASS")

# Coarse constants from the binary dense-variety proof, checked by
# exact exponent arithmetic for rational log densities.
K = 1
for k in range(1,10):
    C = (1<<k)*(2*k+1+2*k*K)+2*k*(k+1)*K
    new = 2*(k+1)**2*K+((1<<(k+1))-1)*((k+1)*C+2)
    for u in (F(0), F(1,3), F(1), F(7,2), F(20)):
        B = (1<<k)*(2*k+1+2*k*K+(k*K+1)*u)+k*(k+1)*K*(u+2)
        assert B <= C*(u+1)
        z = (k+1)*C*(u+1)
        t = (z.numerator+z.denominator-1)//z.denominator+1
        assert t > (k+1)*B
        assert (k+1)**2*K*(u+2)+((1<<(k+1))-1)*t <= new*(u+1)
    K = new
print("binary dense-variety recurrence: arities 2 through 10 PASS")
