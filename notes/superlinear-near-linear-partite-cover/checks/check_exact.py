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


class Q17:
    """Exact rational quadratic field, including signed comparisons."""
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def cast(value):
        return value if isinstance(value, Q17) else Q17(value)

    def __add__(self, other):
        other = self.cast(other)
        return Q17(self.a+other.a, self.b+other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q17(-self.a, -self.b)

    def __sub__(self, other):
        return self+-self.cast(other)

    def __rsub__(self, other):
        return self.cast(other)+-self

    def __mul__(self, other):
        other = self.cast(other)
        return Q17(self.a*other.a+17*self.b*other.b,
                   self.a*other.b+self.b*other.a)

    __rmul__ = __mul__

    def sign(self):
        if self.b == 0:
            return (self.a > 0)-(self.a < 0)
        if self.a == 0 or (self.a > 0) == (self.b > 0):
            return 1 if self.b > 0 else -1
        gap = self.a*self.a-17*self.b*self.b
        return ((gap > 0)-(gap < 0))*(1 if self.a > 0 else -1)


def defect_identities():
    r, q, d = [Poly({tuple(int(i == j) for i in range(3)): 1}) for j in range(3)]
    ell = F(3, 10)*q-d*r
    quad = d*d-F(27, 10)*d+F(19, 25)
    low = (2*r-q)*(F(13, 100)*q-d*d*r)-quad*q*r
    high = (q-2*r)*(F(8, 25)*q+(F(6, 5)*d-F(19, 25))*r)-2*quad*r*r
    K = F(1, 2)*q*(q-r)
    require(not (K-2*ell**2-F(3, 2)*q*ell-low).terms, 'low defect factor')
    require(not (K-2*ell**2-3*r*ell-high).terms, 'high defect factor')
    require(bool((K-2*ell**2-F(3, 2)*q*ell-low+F(1, 100)*q*(2*r-q)).terms),
            'damaged defect factor negative control')
    exact_d = Q17(F(27, 20), -F(1, 4))
    residual = exact_d*exact_d-F(27, 10)*exact_d+F(19, 25)
    require(residual.a == residual.b == 0, 'Qsqrt17 quadratic identity')
    require((exact_d-F(3, 10)).sign() >= 0 and (F(1, 3)-exact_d).sign() >= 0,
            'signed exact d bounds')
    c = 5-5*exact_d
    require((c-F(10, 3)).sign() > 0, 'strict leading constant improvement')
    obstruction = F(1, 10)*(c-F(10, 3))
    expected = Q17(-F(61, 120), F(1, 8))
    require((obstruction-expected).a == (obstruction-expected).b == 0 and
            obstruction.sign() > 0, 'positive excess obstruction')
    print('Both exact defect factorizations, Q(sqrt17) constants and damaged-factor control PASS')


def weighted_check(edges, r):
    from functools import lru_cache
    q = len(edges)
    degree = degree_counts(edges)
    require(max(degree.values(), default=0) <= 4, 'weighted input degree')
    x = Counter(degree.values())
    W = F(x[3], 2)+x[4]
    T = sum(d*(d-1)//2 for d in degree.values())-q*(q-1)//2
    K = F(q*(q-r), 2)
    require(x[4]+3*W == K-F(q, 2)+T+F(x[1], 2), 'weighted incidence identity')
    blocks = [frozenset(i for i, row in enumerate(edges) if row[c] == v)
              for (c, v), d in sorted(degree.items()) if d in (3, 4)]

    def excess(family):
        counts = Counter(pair for block in family for pair in combinations(sorted(block), 2))
        return sum(max(n-1, 0) for n in counts.values()), counts

    initial, _ = excess(blocks)
    require(initial <= T, 'mixed excess budget')
    removed_weight = F(0)
    deletions = 0
    while True:
        before, counts = excess(blocks)
        pair = next((p for p, n in sorted(counts.items()) if n > 1), None)
        if pair is None:
            break
        index = next(i for i, block in enumerate(blocks) if set(pair) <= block)
        removed_weight += F(len(blocks[index])-2, 2)
        blocks.pop(index)
        deletions += 1
        require(excess(blocks)[0] <= before-1, 'mixed strict decrement')
    U = sum((F(len(block)-2, 2) for block in blocks), F(0))
    require(removed_weight <= deletions <= initial <= T, 'weight deletion budget')
    require(U == W-removed_weight and U >= W-T, 'retained mixed weight')
    require(all(len(a & b) <= 1 for a, b in combinations(blocks, 2)), 'mixed linearity')
    D = max(Counter(i for block in blocks for i in block).values(), default=0)
    require(not blocks or 2*D <= q-1, 'mixed point-degree cap')
    require(3*len(blocks) <= q*D and U <= len(blocks), 'small-degree weight bound')
    encoded = [(sum(1 << i for i in block), len(block)-2) for block in blocks]

    @lru_cache(None)
    def maximum(used):
        return max([0]+[weight+maximum(used | mask) for mask, weight in encoded if not used & mask])

    gain = F(maximum(0), 2)
    tau = covers(edges)
    require(tau <= F(q, 2)+F(1, 2)-gain, 'weighted matching exact cover')
    require(W <= r*(F(q, 2)+1-tau), 'part saving')


def weighted_diagnostics():
    count = 0
    for r in (2, 3):
        universe = list(product(range(2), repeat=r))
        for mask in range(1 << len(universe)):
            edges = [e for i, e in enumerate(universe) if mask & (1 << i)]
            if intersecting(edges):
                weighted_check(edges, r)
                count += 1
    weighted_check([(0, 0, k) for k in range(4)], 3)
    p = 3
    plane3 = [tuple((y-c*x) % p for c in range(p))+(x,)
              for x, y in product(range(p), repeat=2)]
    weighted_check(plane3, 4)
    normals = [x for x in product(range(2), repeat=3) if any(x)]
    cube = [tuple(sum(a*b for a, b in zip(x, c)) % 2 for c in normals)
            for x in product(range(2), repeat=3)]
    weighted_check(cube, 7)
    print(f'{count} exhaustive small weighted linearizations plus duplicate/F3/F2 diagnostics PASS')


def general_tangent_checks():
    r, q, z = [Poly({tuple(int(i == j) for i in range(3)): 1}) for j in range(3)]
    for D in range(4, 65):
        L = D+1
        A = (D-1)*q-(2*D+1-2*z)*r
        N = 2*D*q-(D+(D-1)*z)*r
        difference = D*(L*L*q*(q-r)-A**2-3*r*L*A)-N**2+L*L*r*r*(z*z-2*D)
        require(not difference.terms, f'general cleared tangent identity D={D}')
        require(bool((difference+r*r*(z*z-2*D)).terms), 'damaged general identity control')
        require(F((D-3)*(D-2), 2) >= 1, 'nonnegative excess coefficient')
    # The symbolic Lean identity handles every real positive D; these
    # exact coefficients are a separate implementation diagnostic.
    print('61 exact general tangent identities and damaged-identity controls PASS')


def replication_check(edges, r, D):
    q = len(edges)
    degree = degree_counts(edges)
    require(max(degree.values(), default=0) <= D and D >= 4, 'replication degree input')
    x = Counter(degree.values())
    T = sum(d*(d-1)//2 for d in degree.values())-q*(q-1)//2
    W = sum((F(d-2, 2)*n for d, n in x.items() if d >= 3), F(0))
    Y = sum(F((d-3)*(d-2), 2)*n for d, n in x.items() if d >= 4)
    require(3*W+Y == F(q*(q-r), 2)-F(q, 2)+T+F(x[1], 2),
            'arbitrary-degree incidence identity')
    blocks = [frozenset(i for i, row in enumerate(edges) if row[c] == v)
              for (c, v), d in sorted(degree.items()) if d >= 4]

    def excess(family):
        counts = Counter(pair for block in family for pair in combinations(sorted(block), 2))
        return sum(max(n-1, 0) for n in counts.values()), counts

    initial, _ = excess(blocks)
    require(initial <= T, 'general pair-excess budget')
    removed_weight = F(0)
    deletions = 0
    while True:
        before, counts = excess(blocks)
        pair = next((p for p, n in sorted(counts.items()) if n > 1), None)
        if pair is None:
            break
        index = next(i for i, block in enumerate(blocks) if set(pair) <= block)
        d = len(blocks[index])
        removed_weight += F((d-3)*(d-2), 2)
        blocks.pop(index)
        deletions += 1
        require(excess(blocks)[0] <= before-1, 'general strict excess decrement')
    yD = F((D-3)*(D-2), 2)
    require(deletions <= initial <= T and removed_weight <= yD*deletions,
            'arbitrary-degree weighted deletion')
    retained = sum((F((len(b)-3)*(len(b)-2), 2) for b in blocks), F(0))
    require(retained == Y-removed_weight and retained >= Y-yD*T,
            'retained replication weight')
    copies = [(block, F(len(block)-2, 2)) for block in blocks for _ in range(len(block)-3)]
    require(sum((weight for _, weight in copies), F(0)) == retained, 'copy-weight identity')
    counts = Counter(pair for block, _ in copies for pair in combinations(sorted(block), 2))
    require(max(counts.values(), default=0) <= D-3, 'replicated codegree bound')
    degrees = Counter(i for block, _ in copies for i in block)
    a = max(degrees.values(), default=0)
    require(4*len(copies) <= q*a and retained <= F(D-2, 2)*len(copies),
            'small-copy-degree bound')
    tau = covers(edges)
    s = F(q, 2)+1-tau
    require(W <= r*s and s >= 0, 'arbitrary-degree part saving')
    if a:
        point = max(degrees, key=degrees.get)
        star = [b for b in blocks if point in b]
        union = set().union(*star)
        require(len(union) == 1+sum(len(b)-1 for b in star), 'distinct-block star union')
        require(a == sum(len(b)-3 for b in star), 'copy-degree/star alignment')
        require(tau <= len(star)+(q-len(union)+1)//2 and s >= F(a, 2),
                'replicated star cover')

    # A proper greedy colouring diagnoses weighted class averaging;
    # it does not assert Kahn's asymptotic colour-count bound.
    colours = []
    for block, weight in copies:
        chosen = next((c for c in colours if not c[0] & block), None)
        if chosen is None:
            chosen = [set(), F(0)]
            colours.append(chosen)
        chosen[0].update(block)
        chosen[1] += weight
    if colours:
        require(sum(c[1] for c in colours) == retained, 'colour weight accounting')
        gain = max(c[1] for c in colours)
        require(gain >= retained/len(colours), 'weighted colour-class averaging')
        require(tau <= F(q, 2)+F(1, 2)-gain, 'weighted copied matching cover')


def replication_diagnostics():
    count = 0
    for r in (2, 3):
        universe = list(product(range(2), repeat=r))
        for mask in range(1 << len(universe)):
            edges = [e for i, e in enumerate(universe) if mask & (1 << i)]
            if intersecting(edges):
                for D in (4, 5, 8):
                    replication_check(edges, r, D)
                    count += 1
    for p in (3, 5):
        plane = [tuple((y-c*x) % p for c in range(p))+(x,)
                 for x, y in product(range(p), repeat=2)]
        replication_check(plane, p+1, max(4, p))
    replication_check([(0, 0, k) for k in range(5)], 3, 5)
    # Independently compare actual copy incidences to the star expression.
    # A deliberately damaged copied family must be rejected.
    def check_star_alignment(blocks, copies):
        actual = Counter(point for block in copies for point in block)
        expected = Counter()
        for block in blocks:
            for point in block:
                expected[point] += len(block)-3
        require(actual == expected, 'copy incidences do not match distinct-block star')

    five_block = frozenset(range(5))
    check_star_alignment([five_block], [five_block]*2)
    rejected = False
    try:
        check_star_alignment([five_block], [five_block]*3)
    except RuntimeError:
        rejected = True
    require(rejected, 'wrong-copy multiplicity negative control accepted damaged data')
    print(f'{count} exhaustive replication cases, F3/F5 and duplicate-block diagnostics PASS')


if __name__ == '__main__':
    identities()
    transition_identity()
    defect_identities()
    general_tangent_checks()
    scalar_diagnostics()
    finite_diagnostics()
    linearization_diagnostics()
    weighted_diagnostics()
    replication_diagnostics()


