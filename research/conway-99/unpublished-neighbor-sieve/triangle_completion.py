"""Complete labeled exterior adjacencies from contacts and codimension-one pivot rows.

Use python-flint. With a JSON input the fields are shell (39 by 39 adjacency),
words (60 lists of six wing indices, numbered 0 through 35), and optional rows
(a list of [pivot, eight exterior neighbors]). With no input run the positive and negative
controls on an explicit 243-vertex graph.
"""
from itertools import combinations, product
from math import comb
import json
from pathlib import Path
import sys

from flint import fmpq, fmpq_mat as RationalMatrix, fmpz_mat as IntegerMatrix, nmod_poly


def block(matrix, rows, columns):
    return type(matrix)([[matrix[i,j] for j in columns] for i in rows])


def pivot_columns(matrix):
    reduced, _ = RationalMatrix(matrix).rref()
    return [next(j for j in range(reduced.ncols()) if reduced[i,j])
            for i in range(reduced.nrows()) if any(reduced[i,j] for j in range(reduced.ncols()))]


def identity(size):
    return IntegerMatrix([[int(i == j) for j in range(size)] for i in range(size)])


def centered_block(adjacency, degree, restricted_eigenvalue, order):
    n = adjacency.nrows()
    mean = fmpq(degree-restricted_eigenvalue, order)
    return RationalMatrix([[restricted_eigenvalue*int(i == j)+mean-adjacency[i,j]
                            for j in range(n)] for i in range(n)])


def residual_baseline(shell, contacts, degree, restricted_eigenvalue):
    n, far = contacts.nrows(), contacts.ncols()
    gram = centered_block(shell, degree, restricted_eigenvalue, n+far)
    mean = fmpq(degree-restricted_eigenvalue, n+far)
    cross = RationalMatrix([[mean-contacts[i,j] for j in range(far)] for i in range(n)])
    basis = pivot_columns(gram)
    gram_basis = block(gram, basis, basis)
    if any(block(gram_basis, range(k), range(k)).det() <= 0 for k in range(1,len(basis)+1)):
        raise ValueError("indefinite neighborhood")
    products = block(cross, basis, range(far))
    coefficients = gram_basis.inv()*products
    if block(gram, range(n), basis)*coefficients != cross:
        raise ValueError("contact column misses the neighborhood span")
    free = centered_block(IntegerMatrix(far,far), degree, restricted_eigenvalue, n+far)
    return free-products.transpose()*coefficients, len(basis)


def remove_pivots(baseline, rows):
    """Subtract the projection onto independent, fully specified rows."""
    if not rows:
        return baseline
    size = baseline.nrows()
    pivots = [p for p,_ in rows]
    if len(set(pivots)) != len(pivots):
        raise ValueError("repeated pivot")
    known = RationalMatrix([[baseline[p,j]-int(j in neighbors) for j in range(size)]
                            for p, neighbors in rows])
    basis = block(known, range(len(rows)), pivots)
    if basis != basis.transpose() or any(block(basis,range(k),range(k)).det() <= 0
                                         for k in range(1,len(rows)+1)):
        return None
    projected = known.transpose()*basis.inv()*known
    return baseline-projected


def complete_line(remainder):
    size = remainder.nrows()
    norms = [remainder[i,i] for i in range(size)]
    if min(norms) < 0:
        return None
    parity = [[] for _ in range(size)]
    possible = {}
    for i,j in combinations(range(size), 2):
        square = norms[i]*norms[j]
        choices = {}
        for edge in (0,1):
            value = remainder[i,j]-edge
            if value*value == square:
                sign = 0 if not value else (1 if value > 0 else -1)
                choices[sign] = edge
        if not choices:
            return None
        possible[i,j] = choices
        if square and len(choices) == 1:
            sign, = choices
            parity[i].append((j,sign))
            parity[j].append((i,sign))
    signs = [0]*size
    for start in range(size):
        if signs[start] or not norms[start]:
            continue
        signs[start] = 1
        stack = [start]
        while stack:
            i = stack.pop()
            for j,sign in parity[i]:
                expected = signs[i]*sign
                if signs[j] and signs[j] != expected:
                    return None
                if not signs[j]:
                    signs[j] = expected
                    stack.append(j)
    exterior = IntegerMatrix(size,size)
    for (i,j),choices in possible.items():
        exterior[i,j] = exterior[j,i] = choices[signs[i]*signs[j]]
    return exterior


def finish_line(baseline, rows):
    remainder = remove_pivots(baseline,rows)
    return None if remainder is None else complete_line(remainder)


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask -= bit


def exact_neighbors(letters, at_site, demand, optional, forced):
    """All subsets with the required shell incidence, including each forced label."""
    def take(need, mask, chosen):
        for z in chosen:
            for site in letters[z]:
                need[site] -= 1
                if need[site] < 0:
                    return None
                if not need[site]:
                    mask &= ~at_site[site]
        return mask

    need = list(demand)
    for i, count in enumerate(need):
        if count < 0:
            return
        if not count:
            optional &= ~at_site[i]
    optional = take(need,optional,forced)
    if optional is None:
        return

    def search(need, mask, selected):
        best = None
        for site, count in enumerate(need):
            if not count:
                continue
            options = mask & at_site[site]
            ways = comb(options.bit_count(),count)
            if not ways:
                return
            if best is None or ways < best[0]:
                best = (ways,count,options)
        if best is None:
            yield selected
            return
        _,count,options = best
        for group in combinations(indices(options),count):
            updated = need.copy()
            remaining = take(updated,mask & ~options,group)
            if remaining is not None:
                yield from search(updated,remaining,selected+group)

    yield from search(need,optional,tuple(forced))


def complete_from_contacts(shell, contacts, baseline, dimension, accept):
    """Search independent rows. Every recursive branch consumes one dimension."""
    size = baseline.nrows()
    near = contacts.nrows()
    letters = [tuple(i for i in range(near) if contacts[i,j]) for j in range(size)]
    at_site = [sum(1 << j for j in range(size) if contacts[i,j]) for i in range(near)]
    demand = IntegerMatrix([[2]*size]*near)-contacts-shell*contacts
    overlap = contacts.transpose()*contacts

    def search(remainder, dim):
        if dim == 1:
            result = complete_line(remainder)
            return result if result is not None and accept(result) else None
        norms = [remainder[j,j] for j in range(size)]
        if min(norms) < 0:
            return None
        # Choose the smallest positive diagonal, which gives a narrow Cauchy interval.
        active = [j for j in range(size) if norms[j] > 0]
        if not active:
            return None
        p = min(active,key=norms.__getitem__)
        optional = 0
        forced = []
        for j in range(size):
            if j == p:
                continue
            bound = norms[p]*norms[j]
            zero = remainder[p,j]**2 <= bound
            one = overlap[p,j] <= 1 and (remainder[p,j]-1)**2 <= bound
            if not zero and not one:
                return None
            if not zero:
                forced.append(j)
            elif one:
                optional |= 1 << j
        for neighbors in exact_neighbors(letters,at_site,[int(demand[i,p]) for i in range(near)],
                                         optional,forced):
            chosen = set(neighbors)
            row = RationalMatrix([[remainder[p,j]-int(j in chosen) for j in range(size)]])
            updated = remainder-row.transpose()*row/norms[p]
            graph = search(updated,dim-1)
            if graph is not None:
                return graph
        return None

    return search(baseline,dimension)


def assemble(shell, contacts, exterior):
    n, far = contacts.nrows(), contacts.ncols()
    rows = [[shell[i,j] for j in range(n)]+[contacts[i,j] for j in range(far)] for i in range(n)]
    rows += [[contacts[j,i] for j in range(n)]+[exterior[i,j] for j in range(far)] for i in range(far)]
    return IntegerMatrix(rows)


def is_graph(adjacency, degree):
    n = adjacency.nrows()
    if adjacency != adjacency.transpose() or any(adjacency[i,i] for i in range(n)):
        return False
    if any(v not in (0,1) for v in adjacency.entries()):
        return False
    return adjacency*adjacency+adjacency == (degree-2)*identity(n)+IntegerMatrix([[2]*n]*n)


def run_input(path):
    data = json.loads(path.read_text())
    shell = IntegerMatrix(data["shell"])
    words = data["words"]
    if (shell.nrows(),shell.ncols(),len(words)) != (39,39,60):
        raise ValueError("expected a 39-site shell and 60 words")
    contacts = IntegerMatrix(39,60)
    for j,word in enumerate(words):
        if len(set(word)) != 6 or any(i not in range(36) for i in word):
            raise ValueError("bad wing contact word")
        for i in word:
            contacts[3+i,j] = 1
    if shell*shell+shell+contacts*contacts.transpose() != 12*identity(39)+IntegerMatrix([[2]*39]*39):
        print("The shell contacts violate a common-neighbor count.")
        return
    baseline, rank = residual_baseline(shell,contacts,14,3)
    rows = [(p,set(neighbors)) for p,neighbors in data.get("rows",[])]
    if len(rows) > 43-rank or any(p not in range(60) or len(neighbors) != 8 or
                                  not neighbors <= set(range(60))-{p} for p,neighbors in rows):
        raise ValueError("bad partial exterior rows")
    remainder = remove_pivots(baseline,rows)
    valid = lambda f: is_graph(assemble(shell,contacts,f),14)
    exterior = (None if remainder is None else
                complete_from_contacts(shell,contacts,remainder,44-rank-len(rows),valid))
    if exterior is not None:
        adjacency = assemble(shell,contacts,exterior)
        if is_graph(adjacency,14):
            print(json.dumps([[int(adjacency[i,j]) for j in range(99)] for i in range(99)]))
            return
    print("No graph for these labeled contacts and pivot rows.")


def ternary_control_graph():
    # The order-11 powers in F_243 give eleven directions in a five-dimensional
    # ternary space. Verify the entire graph equation before using this control.
    x = nmod_poly([0,1],3)
    modulus = x**5+2*x**3+x**2+2*x+2
    directions = []
    for k in range(11):
        power = x**k % modulus
        v = tuple(int(power[i]) for i in range(5))
        directions += [v,tuple(-a%3 for a in v)]
    points = list(product(range(3),repeat=5))
    index = {v:i for i,v in enumerate(points)}
    adjacency = IntegerMatrix(243,243)
    for i,v in enumerate(points):
        for direction in directions:
            j = index[tuple((a+b)%3 for a,b in zip(v,direction))]
            adjacency[i,j] = 1
    assert is_graph(adjacency,22)
    step = directions[0]
    triangle = [0,index[step],index[tuple(-a%3 for a in step)]]
    return adjacency,triangle


def positive_control():
    adjacency,triangle = ternary_control_graph()
    near = [i for i in range(243) if i in triangle or any(adjacency[i,j] for j in triangle)]
    far = sorted(set(range(243))-set(near))
    assert (len(near),len(far)) == (63,180)
    shell,contacts,exterior = (block(adjacency,near,near),block(adjacency,near,far),
                               block(adjacency,far,far))
    baseline, shell_rank = residual_baseline(shell,contacts,22,4)
    pivots = pivot_columns(baseline-exterior)
    rows = [(p,{j for j in range(180) if exterior[p,j]}) for p in pivots[:-1]]
    assert finish_line(baseline,rows) == exterior
    partial = remove_pivots(baseline,rows[:-1])
    found = complete_from_contacts(shell,contacts,partial,2,
                                   lambda f: is_graph(assemble(shell,contacts,f),22))
    assert found == exterior
    perturbed = RationalMatrix(baseline)
    perturbed[pivots[-1],pivots[-1]] -= 100
    assert finish_line(perturbed,rows) is None
    print("243-vertex positive and negative controls passed.",
          "Neighborhood rank", shell_rank, "and residual rank", len(pivots))


if __name__ == '__main__':
    run_input(Path(sys.argv[1])) if len(sys.argv) > 1 else positive_control()
