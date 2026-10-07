"""Exact diagnostics for incidence replication; not a proof of Input K."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def intersecting(edges):
    return all(a & b for a, b in combinations(edges, 2))


def cover_number(edges):
    if not edges:
        return 0
    vertices = sorted(set().union(*edges))
    masks = [sum(1 << i for i, edge in enumerate(edges) if v in edge)
             for v in vertices]
    full = (1 << len(edges))-1
    for k in range(len(edges)+1):
        for choice in combinations(masks, k):
            total = 0
            for mask in choice:
                total |= mask
            if total == full:
                return k
    raise RuntimeError('finite cover enumeration failed')


def pair_counts(blocks):
    return Counter(pair for block in blocks for pair in combinations(sorted(block), 2))


def block_excess(blocks):
    return sum(max(0, d-1) for d in pair_counts(blocks).values())


def incidence_check(edges, r, exact_cover=True):
    require(len(set(edges)) == len(edges), 'simple input')
    require(all(len(edge) == r for edge in edges), 'uniform input')
    require(intersecting(edges), 'intersecting input')
    q = len(edges)
    degrees = Counter(v for edge in edges for v in edge)
    n = len(degrees)
    T = sum(len(a & b)-1 for a, b in combinations(edges, 2))
    require(sum(degrees.values()) == q*r, 'incidence identity')
    require(sum(d*(d-1)//2 for d in degrees.values()) == q*(q-1)//2+T,
            'intersection count identity')
    require(sum(d*d for d in degrees.values()) == q*(q+r-1)+2*T,
            'squared-degree identity')
    full_weight = sum((d-1)*(d-2)//2 for d in degrees.values())
    require(full_weight == q*(q-1)//2+T-q*r+n, 'copy-weight identity')
    for k in range(1, 7):
        gap = sum((d-k)*(d-k-1) for d in degrees.values())
        require(gap >= 0, 'integer gap nonnegative')
        require(gap == k*(k+1)*n-2*k*q*r+q*(q-1)+2*T,
                'integer vertex-count identity')
    if q:
        require(n*(q*(q+r-1)+2*T) >= q*q*r*r, 'Cauchy count')

    blocks = [frozenset(i for i, edge in enumerate(edges) if v in edge)
              for v, d in sorted(degrees.items()) if d >= 2]
    require(block_excess(blocks) == T, 'all-block excess')
    D = max(degrees.values(), default=1)
    gD = (D-1)*(D-2)//2
    retained = list(blocks)
    deleted = 0
    while True:
        counts = pair_counts(retained)
        repeated = next((p for p, d in sorted(counts.items()) if d > 1), None)
        if repeated is None:
            break
        before = block_excess(retained)
        index = next(i for i, block in enumerate(retained) if set(repeated) <= block)
        retained.pop(index)
        deleted += 1
        require(block_excess(retained) <= before-1, 'strict deletion decrement')
    require(deleted <= T, 'deletion budget')
    require(all(len(a & b) <= 1 for a, b in combinations(retained, 2)),
            'retained linearity')
    weight = sum((len(block)-1)*(len(block)-2)//2 for block in retained)
    require(weight >= full_weight-gD*T, 'weight-loss bound')
    copies = [block for block in retained for _ in range(len(block)-1)]
    copy_degree = Counter(i for block in copies for i in block)
    copy_codegree = pair_counts(copies)
    require(max(copy_degree.values(), default=0) <= max(0, q-1),
            'replicated degree bound')
    require(max(copy_codegree.values(), default=0) <= max(0, D-1),
            'replicated codegree bound')
    require(sum(F(len(block)-2, 2) for block in copies) == weight,
            'replicated weight')
    require(0 <= weight <= q*(q-1)//2, 'weight capacity')

    # Greedy colouring has its ACTUAL colour count. We never substitute
    # Kahn's asymptotic count for the small examples below.
    classes = []
    supports = []
    for block in copies:
        index = next((i for i, support in enumerate(supports) if not support & block), None)
        if index is None:
            classes.append([block])
            supports.append(set(block))
        else:
            classes[index].append(block)
            supports[index].update(block)
    if classes:
        weights = [sum(F(len(block)-2, 2) for block in cls) for cls in classes]
        require(max(weights) >= F(weight, len(classes)), 'weighted averaging')
        for cls, saving in zip(classes, weights):
            require(len(set(cls)) == len(cls), 'matching cannot select repeated copies')
            used = sum(len(block) for block in cls)
            size = len(cls)+(q-used+1)//2
            require(F(size) <= F(q, 2)+F(1, 2)-saving, 'matching cover accounting')
            if exact_cover:
                require(cover_number(edges) <= size, 'independent exact cover comparison')
    if exact_cover:
        require(cover_number(edges) <= (q+1)//2, 'pair cover baseline')
    return len(copies)


def finite_families():
    count = 0
    nonpartite = 0
    for r, N in ((2, 4), (3, 5)):
        universe = [frozenset(e) for e in combinations(range(N), r)]
        for mask in range(1 << len(universe)):
            edges = [e for i, e in enumerate(universe) if mask & (1 << i)]
            if intersecting(edges):
                incidence_check(edges, r)
                count += 1
    # Fano plane is linear and has tau=3. Its triples are not 3-partite:
    # every pair of its seven vertices is on a triple, precluding a
    # three-colouring with all triples rainbow.
    fano = [frozenset((i, j, i ^ j)) for i in range(1, 8) for j in range(i+1, 8)]
    fano = sorted(set(fano), key=lambda e: tuple(sorted(e)))
    require(len(fano) == 7 and cover_number(fano) == 3, 'Fano exact cover')
    incidence_check(fano, 3)
    nonpartite += 1
    # A duplicated-incidence core checks that weight loss and auxiliary
    # deletion concern vertices, not deletion of original edges.
    core = [frozenset((0, 1, i)) for i in range(2, 7)]
    incidence_check(core, 3)
    require(cover_number(core) == 1, 'nonlinear shared-core cover')
    print(f'{count} exhaustive intersecting set families and {nonpartite} Fano diagnostic PASS')


def envelope(x):
    k = max(1, (x.numerator+x.denominator-1)//x.denominator)
    return F(k-1, k+1)+x/F(k*(k+1))


def scalar_checks():
    count = 0
    for denominator in range(1, 19):
        for numerator in range(12*denominator+1):
            x = F(numerator, denominator)
            value = envelope(x)
            require(value == min(F(k-1, k+1)+x/F(k*(k+1)) for k in range(1, 15)),
                    'envelope branch minimum')
            require(value <= x/(1+x), 'harmonic comparison')
            for k in range(1, 13):
                hk = F(k-1, k+1)+x/F(k*(k+1))
                hn = F(k, k+2)+x/F((k+1)*(k+2))
                require(hk-hn == F(2, k*(k+1)*(k+2))*(x-k), 'adjacent-line identity')
                require(x/(1+x)-hk == (x-k+1)*(k-x)/F(k*(k+1)*(1+x)),
                        'harmonic factorization')
            count += 1
    for K in range(2, 13):
        L = K*(K+1)
        for m in range(6*K+1):
            for q in range(m+1):
                require(F(m-q, L)+6*envelope(F(q, 6)) <= 6*envelope(F(m, 6)),
                        'peeling slope transfer')
    # Wrong multiplicity d instead of d-1 actually violates q-1 on
    # the dual triangle, giving a negative control on the certificate.
    triangle_blocks = [frozenset((0, 1)), frozenset((0, 2)), frozenset((1, 2))]
    damaged = [block for block in triangle_blocks for _ in range(len(block))]
    require(max(Counter(i for block in damaged for i in block).values()) > 2,
            'damaged multiplicity rejected')
    for k in range(2, 13):
        P = k*(k+1)
        A = 2*(k+2)*P*P
        for d in range(1, 4*k+1):
            if d not in (k, k+1):
                require(d*abs(d-k) <= (k+2)*(d-k)*(d-k-1), 'bad-degree coefficient')
        for offset in (F(1, 4), F(1, 2), F(3, 4)):
            c = k-1+offset
            theta = offset
            gap = F(k-1, P)*(k-c)
            J = 1+(k+A*(k+2))/(2*theta)
            require(0 < (gap/J)**2 < 1, 'positive conservative gap')
            require(2*c+2*P*envelope(c) <= 2*P, 'vertex-count defect transfer')
            for u in (F(1, 100), F(1, 4), F(3, 4), F(1)):
                delta = u*u
                bound = delta+(k*u+A*delta+A*(k+1)*u)/(2*theta)
                require(bound <= J*u, 'explicit square-root gap transfer')
    print(f'{count} rational envelope diagnostics, peeling checks and damaged-copy control PASS')
    print('Exact bad-degree and explicit noninteger-gap diagnostics PASS')


def affine_family(p, N):
    points = list(product(range(p), repeat=N))
    directions = []
    for vector in points[1:]:
        first = next(a for a in vector if a)
        if first == 1:
            directions.append(vector)
    edges = [set() for _ in points]
    vertices = []
    for c, direction in enumerate(directions):
        lines = {}
        for i, point in enumerate(points):
            line = tuple(sorted(tuple((a+t*b) % p for a, b in zip(point, direction))
                                for t in range(p)))
            lines.setdefault(line, []).append(i)
        require(len(lines) == p**(N-1), 'parallel-class size')
        for line, indices in sorted(lines.items()):
            require(len(indices) == p, 'line incidence size')
            label = len(vertices)
            vertices.append((c, line))
            for i in indices:
                edges[i].add(label)
    r = len(directions)
    family = [frozenset(edge) for edge in edges]
    require(r == (p**N-1)//(p-1), 'direction count')
    require(len(vertices) == r*p**(N-1), 'active vertex count')
    require(all(len(a & b) == 1 for a, b in combinations(family, 2)), 'unique joining line')
    degrees = Counter(v for edge in family for v in edge)
    require(set(degrees.values()) == {p}, 'regular degree profile')
    parallel = [i for i, (c, _) in enumerate(vertices) if c == 0]
    require(all(edge & set(parallel) for edge in family), 'parallel-class cover')
    require(len(parallel)*p == len(family), 'degree-cap lower certificate meets cover')
    incidence_check(family, r, exact_cover=False)
    return r, len(family), len(parallel)


def construction_checks():
    for p, N in ((2, 2), (2, 3), (2, 4), (3, 2), (3, 3)):
        r, m, tau = affine_family(p, N)
        print(f'Affine equality certificate F{p}^{N}: r={r}, m={m}, tau={tau} PASS')
    for m, r in ((3, 2), (6, 5), (5, 9)):
        edges = [set() for _ in range(m)]
        vertex = 0
        for i, j in combinations(range(m), 2):
            edges[i].add(vertex)
            edges[j].add(vertex)
            vertex += 1
        for edge in edges:
            while len(edge) < r:
                edge.add(vertex)
                vertex += 1
        family = [frozenset(e) for e in edges]
        require(cover_number(family) == (m+1)//2, 'private-padded pair construction')
        incidence_check(family, r)
    print('Exact interval-endpoint pair constructions PASS')


if __name__ == '__main__':
    scalar_checks()
    finite_families()
    construction_checks()
