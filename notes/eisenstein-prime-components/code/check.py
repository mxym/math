#!/usr/bin/env python3
"""Independent exact-integer checker for the published finite certificates.

It NEVER calls generate.py and uses no solver, randomization or floating point.
Raises ValueError on any malformed mathematical certificate, including under -O.
"""
import gzip
import json
from collections import deque
from math import gcd, isqrt
from pathlib import Path

DIR = Path(__file__).resolve().parent
UNIT_STEPS = ((-1, -1), (-1, 0), (0, -1), (0, 1), (1, 0), (1, 1))
KING_STEPS = ((-1, -1), (-1, 0), (-1, 1), (0, -1),
              (0, 1), (1, -1), (1, 0), (1, 1))
GENS = ((2, 0), (1, -1), (3, 1), (2, -1), (4, 1), (3, -1))


def demand(condition, message):
    if not condition:
        raise ValueError(message)


def filedata(name):
    with gzip.open(DIR / name, 'rt', encoding='ascii') as f:
        return json.load(f)


def norm(z):
    a, b = z
    return a*a - a*b + b*b


def valid_mask(z, mask):
    a, b = z
    if mask & 1 and a % 2 == 0 and b % 2 == 0:
        return False
    if mask & 2 and (a+b) % 3 == 0:
        return False
    if mask & 4 and (a+4*b) % 7 == 0:
        return False
    if mask & 8 and (a+2*b) % 7 == 0:
        return False
    if mask & 16 and (a+9*b) % 13 == 0:
        return False
    if mask & 32 and (a+3*b) % 13 == 0:
        return False
    return True


def squarefree(q):
    return all(q % (d*d) != 0 for d in range(2, isqrt(q)+1))


def check_negative():
    actual = {}
    for name in ('lower_cycles_1_180.json.gz', 'lower_cycles_181_350.json.gz',
                 'lower_cycles_351_455.json.gz', 'lower_cycles_456_545.json.gz'):
        for item in filedata(name):
            q = item['q']
            demand(type(q) is int and 1 <= q < 546 and squarefree(q), 'bad q')
            demand(q not in actual, 'duplicate q')
            start = tuple(item['base'])
            demand(len(start) == 2 and all(type(z) is int and 0 <= z < q for z in start),
                   'bad start')
            demand(gcd(norm(start), q) == 1, 'forbidden start')
            here = start
            steps = item['steps']
            demand(0 < len(steps) <= 3*q*q, 'cycle length out of range')
            for index in steps:
                demand(type(index) is int and 0 <= index < 8, 'bad step index')
                dx, dy = KING_STEPS[index]
                here = here[0]+dx, here[1]+dy
                demand(gcd(norm(here), q) == 1, f'cycle hits sieve q={q}')
            demand((here[0]-start[0]) % q == 0 and
                   (here[1]-start[1]) % q == 0, f'not closed mod q={q}')
            demand(here != start, f'zero displacement q={q}')
            actual[q] = len(steps)
    expected = {q for q in range(1, 546) if squarefree(q)}
    demand(set(actual) == expected, 'squarefree-period coverage incomplete')
    print('LOWER:', len(actual), 'nonzero-voltage cycles; max length', max(actual.values()))
    return actual


def neighbors(z, steps):
    return [(z[0]+da, z[1]+db) for da, db in steps]


def is_connected(vertices, steps):
    if not vertices:
        return False
    remaining = set(vertices)
    seed = next(iter(remaining))
    remaining.remove(seed)
    queue = deque([seed])
    while queue:
        for q in neighbors(queue.popleft(), steps):
            if q in remaining:
                remaining.remove(q)
                queue.append(q)
    return not remaining


def check_endpoint(mask, expected_count, expected_groups, expected_largest):
    data = filedata(f'endpoint_{mask}.json.gz')
    demand(data['q'] == 546 and data['mask'] == mask, 'wrong endpoint metadata')
    indexed = {}
    largest = 0
    groups = data['components']
    for group_id, seq in enumerate(groups):
        group = {tuple(z) for z in seq}
        demand(len(group) == len(seq) and group, 'repeated/empty group')
        demand(len(group) <= expected_largest, 'group exceeds claimed bound')
        demand(is_connected(group, KING_STEPS), 'disconnected listed component')
        for p in group:
            demand(len(p) == 2 and all(type(a) is int for a in p), 'noninteger point')
            demand(valid_mask(p, mask), 'forbidden endpoint point')
            residue = (p[0] % 546, p[1] % 546)
            demand(residue not in indexed, 'duplicate quotient residue')
            indexed[residue] = group_id
            for n in neighbors(p, KING_STEPS):
                demand(not valid_mask(n, mask) or n in group,
                       'endpoint component is not closed under steps')
        largest = max(largest, len(group))
    # This exhaustive residue check is independent of the generator's traversal.
    for a in range(546):
        for b in range(546):
            wanted = valid_mask((a, b), mask)
            present = (a, b) in indexed
            demand(wanted == present, 'endpoint residue omitted or forbidden')
    demand((len(indexed), len(groups), largest) ==
           (expected_count, expected_groups, expected_largest), 'endpoint counts differ')
    print('ENDPOINT:', mask, 'residues', len(indexed), 'components', len(groups),
          'largest', largest)


def mul(p, z):
    a, b = p
    c, d = z
    return a*c-b*d, a*d+b*c-b*d


def divides(beta, alpha):
    c, d = beta
    a, b = alpha
    n = norm(beta)
    return (a*(c-d)+b*d) % n == 0 and (b*c-a*d) % n == 0


def irreducible_by_divisors(z):
    """Finite complete divisor search: one factor has norm <= sqrt(N(z))."""
    n = norm(z)
    if n < 2:
        return False
    limit = isqrt(n)
    # If norm(c+d*w)<=limit then |c|,|d| < 2 sqrt(limit).
    bound = 2*isqrt(limit)+2
    for c in range(-bound, bound+1):
        for d in range(-bound, bound+1):
            nb = c*c-c*d+d*d
            if 2 <= nb <= limit and divides((c, d), z):
                return False
    return True



def check_modular_ideal_equivalence():
    """Independently compare periodic congruences with exact ideal division."""
    for a in range(546):
        for b in range(546):
            z = (a, b)
            demand(valid_mask(z, 63) == (gcd(norm(z), 546) == 1),
                   'norm sieve and six-ideal sieve disagree')
            for i, g in enumerate(GENS):
                demand(divides(g, z) != valid_mask(z, 1 << i),
                       f'incorrect ideal-congruence rule for generator {i}')
    print('IDEAL REDUCTION: all 298116 residues, six exact divisibility tests')



def check_composite_rigidity():
    """Nonzero-voltage witnesses for all 36 single composite replacements.

    Every membership test uses exact Eisenstein divisibility by literal
    composite generators, independently of the generator's CRT flags.
    """
    proofs=filedata('composite_replacement_cycles.json.gz')
    demand(len(proofs)==36,'incorrect number of replacement cases')
    expected=set()
    for p7 in (2,3):
        for p13 in (4,5):
            selected=(0,1,p7,p13)
            unused=set(range(6))-set(selected)
            for j in selected:
                for extra in unused | ({1} if j==1 else set()):
                    expected.add((selected,j,extra))
    seen=set()
    max_length=0
    for item in proofs:
        selected=tuple(item['selected'])
        j=item['slot']
        extra=item['extra']
        key=(selected,j,extra)
        demand(key in expected and key not in seen, 'missing/repeated replacement case')
        seen.add(key)
        other=tuple(k for k in selected if k!=j)
        composite=mul(GENS[j],GENS[extra])
        def allowed(point):
            return (not any(divides(GENS[k],point) for k in other)
                    and not divides(composite,point))
        start=tuple(item['base'])
        demand(len(start)==2 and
               all(type(z) is int and 0<=z<546 for z in start)
               and allowed(start),'bad replacement walk start')
        coords=start
        steps=item['steps']
        demand(0<len(steps)<=4*546*546,'bad replacement walk length')
        for idx in steps:
            demand(type(idx) is int and 0<=idx<len(KING_STEPS),
                   'bad composite path index')
            da,db=KING_STEPS[idx]
            coords=coords[0]+da,coords[1]+db
            demand(allowed(coords),'replacement walk crosses a deleted ideal')
        demand(coords!=start and all((coords[i]-start[i])%546==0 for i in (0,1)),
               'zero-voltage or nonclosing replacement walk')
        max_length=max(max_length,len(steps))
    demand(seen==expected,'unproved composite replacement')
    print('COMPOSITE RIGIDITY: 36 valid nonzero-voltage walks, maximum length',
          max_length)


def check_f6_hexagons():
    centers = ((0, 0), (2, 4), (4, 2))
    groups = []
    residues = set()
    for center in centers:
        points = {(center[0]+a, center[1]+b) for a, b in UNIT_STEPS}
        demand(len(points) == 6 and is_connected(points, UNIT_STEPS), 'not a hexagon')
        for p in points:
            demand(gcd(norm(p), 6) == 1, 'forbidden hexagon vertex')
            res = p[0] % 6, p[1] % 6
            demand(res not in residues, 'overlap mod 6')
            residues.add(res)
            for n in neighbors(p, UNIT_STEPS):
                demand(gcd(norm(n), 6) != 1 or n in points, 'hexagon not closed')
        groups.append(points)
    for a in range(6):
        for b in range(6):
            demand(((a,b) in residues) == (gcd(norm((a,b)),6)==1),
                   'missing allowed mod-6 vertex')
    print('HEXAGONS: 3 quotient components of size 6')


def check_closure(size, q, steps, count, prime_count):
    data = filedata(f'exceptional_closure_{size}.json.gz')
    demand(data['q'] == q and data['steps'] == size, 'bad closure metadata')
    C = {tuple(z) for z in data['points']}
    demand(len(C) == len(data['points']) == count, 'closure cardinality wrong')
    gens = GENS[:2] if size == 6 else GENS
    exception = {mul(u, g) for u in UNIT_STEPS for g in gens}
    demand(exception <= C, 'exceptional prime missing')
    demand(len(exception) == 6*len(gens), 'repeated exceptional prime')
    for point in C:
        demand(point in exception or gcd(norm(point),q) == 1,
               'non-exception forbidden in closure')
        for n in neighbors(point, steps):
            demand(n in C or (n not in exception and gcd(norm(n),q) != 1),
                   'missing permitted neighbor in finite closure')
    # Verify this finite invariant is reachable from the exceptional points.
    found = set(exception)
    todo = deque(exception)
    while todo:
        for y in neighbors(todo.popleft(), steps):
            if y in C and y not in found:
                found.add(y)
                todo.append(y)
    demand(found == C, 'extra unreachable vertices in closure')
    irreducibles = {p for p in C if irreducible_by_divisors(p)}
    demand(len(irreducibles) == prime_count, 'wrong exact irreducible count')
    demand(exception <= irreducibles, 'exceptional generator not irreducible')
    demand(is_connected(irreducibles, steps), 'prime subset not connected')
    print('CLOSURE:', size, 'vertices',len(C),'irreducibles',len(irreducibles),
          'all irreducibles connected')


if __name__ == '__main__':
    check_negative()
    check_modular_ideal_equivalence()
    check_composite_rigidity()
    check_f6_hexagons()
    check_endpoint(63, 93312, 16536, 74)
    check_endpoint(23, 117936, 4368, 94)
    check_endpoint(27, 117936, 4368, 125)
    check_endpoint(39, 117936, 4368, 125)
    check_endpoint(43, 117936, 4368, 94)
    check_closure(6, 6, UNIT_STEPS, 54, 48)
    check_closure(8, 546, KING_STEPS, 138, 132)
    print('ALL EXACT CERTIFICATES VERIFIED')
