"""Exact algebra and finite diagnostics; the universal proof is paper.md."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


# Sparse rational polynomials in r,q,t. Identity checking never samples.
class Poly:
    def __init__(self, terms):
        if isinstance(terms, (int, F)):
            terms = {(0, 0, 0): F(terms)}
        self.terms = {k: F(v) for k, v in terms.items() if v}

    @staticmethod
    def cast(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        out = dict(self.terms)
        for k, v in self.cast(other).terms.items():
            out[k] = out.get(k, 0) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        out = {}
        for a, av in self.terms.items():
            for b, bv in self.cast(other).terms.items():
                k = tuple(x+y for x, y in zip(a, b))
                out[k] = out.get(k, 0) + av*bv
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        out = Poly(1)
        for _ in range(n):
            out *= self
        return out


def identities():
    r, q, t = [Poly({tuple(int(i == j) for i in range(3)): 1}) for j in range(3)]
    B8r = 40*r*t-17*r*q+5*q*(q-1)-20*r
    base160r = 800*r*t-289*r*r-570*r-25
    require(not (20*B8r-base160r-(10*q-17*r-5)**2).terms, 'square identity')
    at2r = 40*r*t-14*r*r-30*r
    factor = (q-2*r)*(5*q-7*r-5)
    require(not (B8r-at2r-factor).terms, 'threshold factorization')
    damaged = (20*B8r-base160r-(10*q-17*r-6)**2).terms
    require(bool(damaged), 'damaged identity negative control')
    u = q
    require(not (u*u-13*u+60-(u-F(13, 2))**2-F(71, 4)).terms,
            'degree-three positive square')
    print('Exact sparse-polynomial identities and damaged-identity control PASS')


def intersecting(edges):
    return all(any(x == y for x, y in zip(a, b)) for a, b in combinations(edges, 2))


def covers(edges):
    vertices = sorted({(c, x) for edge in edges for c, x in enumerate(edge)})
    full = (1 << len(edges))-1
    masks = [sum(1 << i for i, edge in enumerate(edges) if edge[c] == x)
             for c, x in vertices]
    for k in range(len(edges)+1):
        for choice in combinations(masks, k):
            union = 0
            for mask in choice:
                union |= mask
            if union == full:
                return k
    raise RuntimeError('failed to find a cover')


def degree_counts(edges):
    return Counter((c, x) for edge in edges for c, x in enumerate(edge))


def residual_check(edges, r):
    q = len(edges)
    degrees = degree_counts(edges)
    require(max(degrees.values(), default=0) <= 4, 'residual degree restriction')
    x = Counter(degrees.values())
    W = F(x[3], 2)+x[4]
    require(sum(k*n for k, n in x.items()) == q*r, 'incidence count')
    pair_count = sum(d*(d-1)//2 for d in degrees.values())
    pair_direct = sum(sum(a == b for a, b in zip(e, f)) for e, f in combinations(edges, 2))
    require(pair_count == pair_direct, 'independent intersection-pair count')
    require(F(q*(q-1), 2) <= pair_count <= F(q*r, 2)+4*W,
            'pair bounds')
    best_saving = max((sum(F(1, 2) if d == 3 else 1 if d == 4 else 0
                           for (part, _), d in degrees.items() if part == c)
                       for c in range(r)), default=0)
    require(best_saving >= W/r, 'part averaging')
    tau = covers(edges)
    require(tau <= F(q, 2)+F(1, 2)-W/r, 'explicit part cover')
    require(tau <= F(q, 2)+F(1, 2)-F(q*(q-r-1), 8*r), 'quadratic residual')
    require(4*tau <= q+r+4, 'degree-four residual cover')
    return tau


def full_check(edges, r):
    tau = covers(edges)
    require(len(edges) >= 5*tau-F(7*r, 4)-5, 'strong theorem diagnostic')
    require(len(edges) >= 5*tau-F(289*r, 160)-F(57, 16)-F(5, 32*r),
            'elementary theorem diagnostic')
    current, k = list(edges), 0
    while True:
        degrees = degree_counts(current)
        vertex = next((v for v, d in sorted(degrees.items()) if d >= 5), None)
        if vertex is None:
            break
        c, x = vertex
        current = [edge for edge in current if edge[c] != x]
        k += 1
    residual_tau = residual_check(current, r)
    require(len(edges) >= len(current)+5*k, 'peeling count')
    require(tau <= k+residual_tau, 'peeling cover')


def finite_diagnostics():
    count = 0
    for r in (2, 3):
        universe = list(product(range(2), repeat=r))
        for mask in range(1 << len(universe)):
            edges = [e for i, e in enumerate(universe) if mask & (1 << i)]
            if intersecting(edges):
                full_check(edges, r)
                count += 1
    print(f'All {count} intersecting binary-width families in ranks 2 and 3 PASS')
    for p in (3, 5):
        # Truncated projective plane: all p^2 affine points, p+1 directions.
        edges = [tuple((y-c*x) % p for c in range(p))+(x,)
                 for x, y in product(range(p), repeat=2)]
        require(intersecting(edges), 'projective-plane intersection')
        require(covers(edges) == p, 'exact projective-plane cover number')
        full_check(edges, p+1)
    print('Exact F3/F5 truncated-projective-plane cover and peeling diagnostics PASS')


def scalar_diagnostics():
    checked = 0
    for r in range(2, 61):
        for q in range(4*r+1):
            A = -F(5*r, 4)-F(q, 4)-5
            B = -F(17*q, 8)+F(5*q*(q-1), 8*r)-F(5, 2)
            elementary = -F(289*r, 160)-F(57, 16)-F(5, 32*r)
            require(B >= elementary, 'complete-square finite diagnostic')
            require(max(A, B) >= -F(7*r, 4)-5, 'threshold combination')
            checked += 1
    print(f'{checked} exact rational scalar diagnostics PASS (not the universal proof)')


def transition_identity():
    r, q, _ = [Poly({tuple(int(i == j) for i in range(3)): 1}) for j in range(3)]
    ell = F(3, 10)*q-F(1, 3)*r
    difference = F(1, 2)*q*(q-r)-2*ell**2-3*r*ell
    factor = F(1, 225)*(3*q-5*r)*(24*q-35*r)
    require(not (difference-factor).terms, '10/3 transition polynomial')
    require(bool((difference-F(1, 224)*(3*q-5*r)*(24*q-35*r)).terms),
            'damaged transition negative control')
    print('10/3 exact transition identity and damaged-factor control PASS')


def linearization_check(edges, r):
    q = len(edges)
    degree = degree_counts(edges)
    require(max(degree.values(), default=0) <= 4, 'linearization input degree')
    x = Counter(degree.values())
    W = F(x[3], 2)+x[4]
    S = sum(d*(d-1)//2 for d in degree.values())
    T = S-q*(q-1)//2
    require(T >= 0, 'total excess')
    blocks = [frozenset(i for i, row in enumerate(edges) if row[c] == v)
              for (c, v), d in sorted(degree.items()) if d == 4]

    def pair_counts(family):
        return Counter(pair for block in family for pair in combinations(sorted(block), 2))

    def excess(family):
        return sum(max(0, n-1) for n in pair_counts(family).values())

    initial = excess(blocks)
    require(initial <= T, 'degree-four excess dominated by full excess')
    deleted = 0
    while True:
        counts = pair_counts(blocks)
        pair = next((p for p, n in sorted(counts.items()) if n > 1), None)
        if pair is None:
            break
        before = excess(blocks)
        index = next(i for i, block in enumerate(blocks) if set(pair) <= block)
        blocks.pop(index)
        deleted += 1
        require(excess(blocks) <= before-1, 'strict excess decrement')
    e = len(blocks)
    require(deleted <= initial, 'deletion budget')
    require(all(len(a & b) <= 1 for a, b in combinations(blocks, 2)), 'linearity')
    require(e >= x[4]-T == F(q*(q-1), 2)-F(q*r, 2)-3*W+F(x[1], 2),
            'exact saving-sensitive identity')
    tau = covers(edges)
    s = F(q, 2)+1-tau
    require(s >= 0 and W <= r*s, 'partite saving bound')
    auxiliary_degree = Counter(i for block in blocks for i in block)
    D = max(auxiliary_degree.values(), default=0)
    require(4*e <= q*D, 'auxiliary incidence')
    if D:
        point = max(auxiliary_degree, key=auxiliary_degree.get)
        star = [block for block in blocks if point in block]
        union = set().union(*star)
        require(len(union) == 1+3*D, 'linear star union')
        require(tau <= D+(q-len(union)+1)//2, 'exact star cover')
        require(s >= F(D, 2), 'star saving')
    return e


def linearization_diagnostics():
    count = 0
    for r in (2, 3):
        universe = list(product(range(2), repeat=r))
        for mask in range(1 << len(universe)):
            edges = [e for i, e in enumerate(universe) if mask & (1 << i)]
            if intersecting(edges):
                linearization_check(edges, r)
                count += 1
    linearization_check([(0, 0, k) for k in range(4)], 3)
    normals = [x for x in product(range(2), repeat=3) if any(x)]
    binary_plane = [tuple(sum(a*b for a, b in zip(x, c)) % 2 for c in normals)
                    for x in product(range(2), repeat=3)]
    require(intersecting(binary_plane), 'F2 cube-plane family intersecting')
    linearization_check(binary_plane, 7)

    def mul4(a, b):
        out = 0
        for i in range(2):
            if b & (1 << i):
                out ^= a << i
        if out & 4:
            out ^= 7  # irreducible polynomial x^2+x+1
        return out

    for a, b, c in product(range(4), repeat=3):
        require(mul4(a, b ^ c) == mul4(a, b) ^ mul4(a, c), 'F4 distributivity')
    plane4 = [tuple(y ^ mul4(c, x) for c in range(4))+(x,)
              for x, y in product(range(4), repeat=2)]
    require(intersecting(plane4) and covers(plane4) == 4, 'F4 plane cover')
    require(linearization_check(plane4, 5) == 20, 'linear F4 block retention')
    print(f'{count} small-family linearizations plus duplicate blocks, F2 planes and F4 plane PASS')


if __name__ == '__main__':
    identities()
    transition_identity()
    scalar_diagnostics()
    finite_diagnostics()
    linearization_diagnostics()


