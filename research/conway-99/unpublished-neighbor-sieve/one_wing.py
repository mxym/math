"""Reconstruct a Conway graph from just the labeled 60 by 60 exterior adjacency.

The exterior labels, in lexicographic order, are the nonmate pairs of 0,...,11
with mate i xor 1. Supply the adjacency as a JSON matrix. Running without an
argument tests the reconstruction on the 243-vertex graph with lambda=1, mu=2.
"""
from math import isqrt
from itertools import combinations, product
import json
from pathlib import Path
import sys

from flint import fmpq_mat as RationalMatrix, fmpz_mat as Matrix
from triangle_completion import block, identity, is_graph, pivot_columns, ternary_control_graph


def right_kernel(matrix):
    reduced, rank = RationalMatrix(matrix).rref()
    n = matrix.ncols()
    pivots = [next(j for j in range(n) if reduced[i,j]) for i in range(rank)]
    free = sorted(set(range(n))-set(pivots))
    basis = RationalMatrix(n,len(free))
    for k,j in enumerate(free):
        basis[j,k] = 1
        for i,p in enumerate(pivots):
            basis[p,k] = -reduced[i,j]
    return basis


def positive_semidefinite(matrix):
    pivots = pivot_columns(matrix)
    if not pivots:
        return True
    basis = block(matrix,pivots,pivots)
    return all(block(basis,range(k),range(k)).det() > 0 for k in range(1,len(pivots)+1))


def column_lattice_index(image, principal, labels):
    """Index in the centered integer lattice, or None for an impossible determinant."""
    rank = principal.nrows()
    basis = block(image.hnf(),range(rank),range(rank))
    numerator = abs(int(basis.det()))
    denominator = int(principal.det())*labels
    quotient, remainder = divmod(numerator*numerator,denominator)
    index = isqrt(quotient)
    return index if not remainder and index*index == quotient else None


def first_wing(n):
    pairs = [(i,j) for i,j in combinations(range(n),2) if i^1 != j]
    mates = Matrix([[int(i^1 == j) for j in range(n)] for i in range(n)])
    contacts = Matrix([[int(i in pair) for pair in pairs] for i in range(n)])
    return pairs,mates,contacts


def candidate_rows(image, support, gram, common, limit):
    """All unoriented signed rows in col(gram) supported exactly on support."""
    total = image.nrows()
    zeros = sorted(set(range(total))-set(support))
    coefficients = right_kernel(block(image,zeros,range(image.ncols())))
    dimension = coefficients.ncols()
    if not 1 <= dimension <= limit:
        return []
    space = image*coefficients
    pivots = pivot_columns(space.transpose())
    transform = space*block(space,pivots,range(dimension)).inv()
    test_pairs = [(y,z) for y,z in combinations(support,2) if common[y,z] == 1]
    rows = []
    for tail in product((-1,1),repeat=dimension-1):
        values = transform*Matrix([[s] for s in (1,*tail)])
        if not all(abs(values[y,0]) == 1 for y in support):
            continue
        row = tuple(int(values[y,0]) for y in range(total))
        if all(row[y]*row[z] == gram[y,z] for y,z in test_pairs):
            rows.append(row)
    return rows


def row_systems(options, supports, gram, common):
    """Return unsigned row choices whose outer products sum to the desired Gram."""
    order = sorted(range(len(options)),key=lambda i:len(options[i]))
    residual = {}
    available = {}
    affected = [list(combinations(s,2)) for s in supports]
    for y,z in combinations(range(gram.nrows()),2):
        available[y,z],residual[y,z] = int(common[y,z]),int(gram[y,z])
        if abs(residual[y,z]) > available[y,z] or (residual[y,z]-available[y,z])%2:
            return
    chosen = [None]*len(options)

    def visit(depth):
        if depth == len(order):
            yield Matrix(chosen)
            return
        site = order[depth]
        changes = affected[site]
        for pair in changes:
            available[pair] -= 1
        for row in options[site]:
            if any(abs(residual[y,z]-row[y]*row[z]) > available[y,z] for y,z in changes):
                continue
            chosen[site] = row
            for y,z in changes:
                residual[y,z] -= row[y]*row[z]
            yield from visit(depth+1)
            for y,z in changes:
                residual[y,z] += row[y]*row[z]
        for pair in changes:
            available[pair] += 1

    yield from visit(0)


def mates(contacts):
    overlap = contacts*contacts.transpose()
    n = contacts.nrows()
    if any(overlap[i,i] != n-2 for i in range(n)):
        return None
    result = Matrix([[int(i != j and overlap[i,j] == 0) for j in range(n)] for i in range(n)])
    if any(overlap[i,j] not in (0,1) for i,j in combinations(range(n),2)):
        return None
    if any(sum(result[i,j] for j in range(n)) != 1 for i in range(n)):
        return None
    return result


def assemble(exterior, layers, matchings, transfer):
    n = layers[0].nrows()
    start = 3+3*n
    size = start+exterior.nrows()
    ans = Matrix(size,size)

    def edge(i,j):
        ans[i,j] = ans[j,i] = 1

    for i,j in combinations(range(3),2):
        edge(i,j)
    for w in range(3):
        base = 3+w*n
        for i in range(n):
            edge(w,base+i)
            for j in range(i+1,n):
                if matchings[w][i,j]:
                    edge(base+i,base+j)
            for y in range(exterior.nrows()):
                if layers[w][i,y]:
                    edge(base+i,start+y)
    for i in range(n):
        edge(3+i,3+n+i)
        edge(3+i,3+2*n+i)
        for j in range(n):
            if transfer[i,j]:
                edge(3+2*n+i,3+n+j)
    for i,j in combinations(range(exterior.nrows()),2):
        if exterior[i,j]:
            edge(start+i,start+j)
    return ans


def completions(exterior, n, stats):
    pairs,m0,b0 = first_wing(n)
    size = len(pairs)
    if exterior.nrows() != size or exterior.ncols() != size:
        raise ValueError("wrong exterior order")
    if exterior != exterior.transpose() or any(v not in (0,1) for v in exterior.entries()):
        return
    if any(exterior[i,i] or sum(exterior[i,j] for j in range(size)) != n-4 for i in range(size)):
        return
    sums = Matrix([[2]*size]*n) - (identity(n)+m0)*b0 - b0*exterior
    if any(v not in (0,1,2) for v in sums.entries()):
        return
    if any(sum(sums[i,y] == 2 for y in range(size)) > 1 for i in range(n)):
        return
    if any(sum(sums[i,y] for i in range(n)) != 4 for y in range(size)):
        return
    gram = 2*(n*identity(size) + Matrix([[2]*size]*size)-exterior-exterior*exterior
              - b0.transpose()*b0)-sums.transpose()*sums
    mask = Matrix([[int(sums[i,y] == 1) for y in range(size)] for i in range(n)])
    common = mask.transpose()*mask
    if any(gram[y,y] != common[y,y] for y in range(size)):
        return
    pivots = pivot_columns(gram)
    if len(pivots) != n-1:
        return
    image = block(gram,range(size),pivots)
    sub = block(gram,pivots,pivots)
    squared = image.transpose()*image
    if not all(positive_semidefinite(a) for a in
               (sub,squared-(2*n-12)*sub,(2*n+4)*sub-squared)):
        return
    index = column_lattice_index(image,sub,n)
    stats["column_index"] = index
    if index is None:
        return
    supports = [[y for y in range(size) if mask[i,y]] for i in range(n)]
    limit = 1+(2*(n-2)*(3*n-4))//((n-1)*(2*n-12))
    options = [candidate_rows(image,s,gram,common,limit) for s in supports]
    stats["row_options"] = [len(o) for o in options]
    if not all(options):
        return
    for rows in row_systems(options,supports,gram,common):
        null = right_kernel(rows.transpose())
        if null.ncols() != 1 or any(abs(v) != 1 for v in null.entries()):
            continue
        signed = Matrix([[int(null[i,0])*rows[i,j] for j in range(size)] for i in range(n)])
        b1,b2 = (sums+signed)/2,(sums-signed)/2
        m1,m2 = mates(b1),mates(b2)
        if m1 is None or m2 is None:
            continue
        transfer = Matrix([[2]*n]*n)-b0*b1.transpose()-identity(n)-m0-m1
        if any(v not in (0,1) for v in transfer.entries()):
            continue
        if any(sum(transfer[i,j] for j in range(n)) != 1 or
               sum(transfer[j,i] for j in range(n)) != 1 for i in range(n)):
            continue
        candidate = assemble(exterior,(b0,b1,b2),(m0,m1,m2),transfer)
        if is_graph(candidate,n+2):
            yield candidate


def control():
    full_graph,parents = ternary_control_graph()
    neighbors = [{j for j in range(243) if full_graph[i,j]} for i in range(243)]
    wing = neighbors[0]-set(parents)
    first = []
    while wing:
        i = min(wing)
        j, = wing & neighbors[i]
        first += [i,j]
        wing -= {i,j}
    arms = [first]
    for p in parents[1:]:
        arm = neighbors[p]-set(parents)
        arms.append([next(iter(neighbors[i]&arm)) for i in first])
    far = set(range(243))-set(parents)-set().union(*arms)
    pairs = first_wing(20)[0]
    exterior_labels = [next(iter(far&neighbors[first[i]]&neighbors[first[j]])) for i,j in pairs]
    order = parents+sum(arms,[])+exterior_labels
    assert len(set(order)) == 243
    full = Matrix([[int(j in neighbors[i]) for j in order] for i in order])
    assert is_graph(full,22)
    exterior = block(full,range(63,243),range(63,243))
    stats = {}
    output = list(completions(exterior,20,stats))
    swap = [0,2,1,*range(3,23),*range(43,63),*range(23,43),*range(63,243)]
    assert len(output) == 1 and output[0] in (full,block(full,swap,swap))
    invalid = Matrix([[int((i-j)%60 in {1,2,3,4,56,57,58,59}) for j in range(60)] for i in range(60)])
    assert not list(completions(invalid,12,{}))
    print("Recovered the 243-vertex graph from its 180-vertex exterior alone.",stats)


if __name__ == "__main__":
    if len(sys.argv) == 1:
        control()
    else:
        f = Matrix(json.loads(Path(sys.argv[1]).read_text()))
        stats = {}
        result = next(completions(f,12,stats),None)
        if result is None:
            print("No completion for this labeled exterior.")
        else:
            print(json.dumps([[int(v) for v in row] for row in result.tolist()]))
