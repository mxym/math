#!/usr/bin/env python3
# Independent test: optimize each binary-output map over a full privacy polytope.
from fractions import Fraction as Q
from itertools import combinations, product


def solve4(rows):
    work = [list(map(Q, row)) for row in rows]
    for i in range(4):
        pivot = next((j for j in range(i,4) if work[j][i]), None)
        if pivot is None:
            return None
        work[i], work[pivot] = work[pivot], work[i]
        d = work[i][i]
        work[i] = [x/d for x in work[i]]
        for j in range(4):
            if j != i:
                d = work[j][i]
                work[j] = [x-d*y for x,y in zip(work[j],work[i])]
    return tuple(row[4] for row in work)


def binary_optimum(eps):
    # Coordinate order 00,01,10,11. The two inequalities compare
    # first-party view at m=0,1 and second-party view at m=0,1.
    # Marginal differences are x01-x10 and x00-x11 respectively.
    facets = [tuple(-int(j == i) for j in range(4))+(0,) for i in range(4)]
    for a in (-1,1):
        facets.extend(((0,a,-a,0,eps),(a,0,0,-a,eps)))
    states = set()
    for faces in combinations(facets, 3):
        x = solve4([(1,1,1,1,1),*faces])
        if x is not None and all(sum(a*b for a,b in zip(f[:4],x)) <= f[4] for f in facets):
            states.add(x)
    assert states
    maps = list(product((0,1), repeat=4))
    errors = {m:max(abs(Q(1,2)-sum(a*b for a,b in zip(m,x))) for x in states)
              for m in maps}
    # Compute directly from all maps, not just the predicted minimizing family.
    optimum = min(errors.values())
    argmins = {m for m,v in errors.items() if v == optimum}
    assert argmins == {(0,0,1,1),(1,1,0,0),(0,1,0,1),(1,0,1,0)}
    assert optimum == eps
    # Includes a negative control: a map with genuine two-coordinate dependency.
    assert errors[(0,1,1,0)] == Q(1,2)
    return len(states)


def additive_boolean():
    count = 0
    for q in (2,3):
        pairs = list(combinations(range(q), 2))
        for mask in range(1 << (q*q)):
            table = [[(mask >> (i*q+j)) & 1 for j in range(q)] for i in range(q)]
            all_zero = all(table[i][j]+table[k][l] == table[i][l]+table[k][j]
                           for (i,k),(j,l) in product(pairs, repeat=2))
            one_axis = (
                len({tuple(row) for row in table}) == 1 or
                all(len(set(row)) == 1 for row in table)
            )
            assert all_zero == one_axis
            count += 1
    return count


def color_compatibility():
    # Enumerate all surjective 3-colorings of the 3 by 3 grid.
    # Test zero-mixed-difference per color via basepoint additive identity.
    balanced_form = 0
    tested = 0
    for cells in product(range(3), repeat=9):
        if len(set(cells)) != 3:
            continue
        tested += 1
        for a in range(3):
            c = [int(v == a) for v in cells]
            if any(c[3*i+j]+c[0] != c[3*i]+c[j]
                   for i in range(1,3) for j in range(1,3)):
                break
        else:
            row = all(len(set(cells[k:k+3])) == 1 for k in range(0,9,3))
            col = len({cells[k:k+3] for k in range(0,9,3)}) == 1
            assert row != col
            balanced_form += 1
    assert balanced_form == 12  # Two choices of coordinate, 3! permutations.
    return tested, balanced_form


for epsilon in (Q(0),Q(1,32),Q(1,8)):
    print(f"Independent q=2 privacy LP eps={epsilon}: {binary_optimum(epsilon)} vertices, all 16 extractors, minimax={epsilon}")
print(f"Independent mixed-difference Boolean tables, q=2,3: {additive_boolean()}")
a,b = color_compatibility()
print(f"Independent three-color common-coordinate test: {a} surjections, {b} zero-mixed-difference cases")
