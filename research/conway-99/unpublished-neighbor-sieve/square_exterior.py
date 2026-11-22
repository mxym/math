"""Recover SRG completions from the exterior of an induced square.

Input is a JSON adjacency on the 51 exterior sites, in any order. Without
arguments, delete an 80-site square neighborhood of the 243-site control
graph and check that the exterior alone recovers the original.
"""
from itertools import combinations
import json
from math import comb, isqrt
from pathlib import Path
import sys

from flint import fmpq_mat as Rational, fmpz_mat as Matrix, nmod_mat
from triangle_completion import block, identity, is_graph, pivot_columns, ternary_control_graph


def positions(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def mask(positions_):
    return sum(1 << i for i in positions_)


def indicator_matrix(words, width):
    return Matrix([[int((w >> i) & 1) for i in range(width)] for w in words])


def parity_checks(gram):
    """Parity-check columns for the saturated rational row space modulo two."""
    echelon = {}
    basis = []
    for i in pivot_columns(gram):
        row = [int(gram[i,j]) for j in range(gram.ncols())]
        while True:
            word = mask(j for j,v in enumerate(row) if v % 2)
            combination = 0
            while word:
                pivot = word.bit_length() - 1
                if pivot not in echelon:
                    break
                reduced, coefficients = echelon[pivot]
                word ^= reduced
                combination ^= coefficients
            if word:
                echelon[word.bit_length()-1] = word, combination ^ (1 << len(basis))
                basis.append(row)
                break
            for h in positions(combination):
                row = [a+b for a,b in zip(row,basis[h])]
            assert all(v % 2 == 0 for v in row)
            row = [v//2 for v in row]

    width = gram.ncols()
    columns = [0]*width
    for i,j in enumerate(sorted(set(range(width))-set(echelon))):
        columns[j] = 1 << i
    for pivot,(word,_) in sorted(echelon.items()):
        for j in positions(word ^ (1 << pivot)):
            columns[pivot] ^= columns[j]
    return columns


def supported_code(allowed, columns):
    """Basis for binary words supported on allowed with zero check sum."""
    pivots, kernel = {}, []
    for j in positions(allowed):
        value, support = columns[j], 1 << j
        while value:
            p = value.bit_length()-1
            if p not in pivots:
                break
            old, word = pivots[p]
            value ^= old
            support ^= word
        if value:
            pivots[value.bit_length()-1] = value,support
        else:
            kernel.append(support)
    return kernel


def candidate_contacts(exterior, gram, degree):
    size = exterior.nrows()
    columns = parity_checks(gram)
    permitted = [mask(j for j in range(size) if gram[i,j]) for i in range(size)]
    neighbors = [mask(j for j in range(size) if exterior[i,j]) for i in range(size)]
    low, high = degree-6, degree-3
    candidates = set()

    def visit(chosen, available):
        if chosen.bit_count() > high or (available|chosen).bit_count() < low:
            return
        kernel = supported_code(chosen|available,columns)
        if len(kernel) <= 11:
            words = [0]
            for basis_word in kernel:
                words += [w ^ basis_word for w in words]
            for w in words:
                if w & chosen != chosen or not low <= w.bit_count() <= high:
                    continue
                if all(not (w & ~permitted[i]) and (w & neighbors[i]).bit_count() <= 1
                       for i in positions(w)):
                    candidates.add(w)
            return
        while available:
            b = available & -available
            available ^= b
            visit(chosen|b,available & permitted[b.bit_length()-1])

    visit(0,(1 << size)-1)
    return sorted(candidates)


def contact_systems(words, gram, count):
    """Select distinct binary rows with exactly the prescribed Gram."""
    size = gram.nrows()
    if len(words) < count:
        return
    if len(words) == count:
        contacts = indicator_matrix(words,size)
        if contacts.transpose()*contacts == gram:
            yield contacts
        return

    at = [mask(i for i,w in enumerate(words) if (w >> j) & 1) for j in range(size)]
    constraints = [(at[i]&at[j],int(gram[i,j])) for i in range(size)
                   for j in range(i+1) if gram[i,j]]
    constraints.append(((1 << len(words))-1,count))

    def visit(chosen, available):
        required = rejected = 0
        branch = None
        for members,target in constraints:
            left = target - (members&chosen).bit_count()
            options = members & available
            capacity = options.bit_count()
            if not 0 <= left <= capacity:
                return
            if left == 0:
                rejected |= options
            elif capacity == left:
                required |= options
            else:
                cost = comb(capacity,left)
                if branch is None or cost < branch[0]:
                    branch = cost,options,left
        if required & rejected:
            return
        if required or rejected:
            yield from visit(chosen|required,available & ~(rejected|required))
        elif branch is None:
            contacts = indicator_matrix([words[i] for i in positions(chosen)],size)
            if contacts.nrows() == count and contacts.transpose()*contacts == gram:
                yield contacts
        else:
            _,options,left = branch
            for selected in combinations(positions(options),left):
                yield from visit(chosen|mask(selected),available & ~options)

    yield from visit(0,(1 << len(words))-1)


class BinaryPreimages:
    """Binary solutions to x B = target over the rationals."""
    def __init__(self, contacts):
        self.contacts = contacts
        self.rows = pivot_columns(contacts.transpose())
        self.columns = pivot_columns(contacts)
        self.free = sorted(set(range(contacts.nrows())) - set(self.rows))
        self.inverse = Rational(block(contacts,self.rows,self.columns)).inv()
        self.directions = [Rational([[-contacts[i,j] for j in self.columns]])*self.inverse
                           for i in self.free]

    def solve(self, target):
        start = Rational([[target[j] for j in self.columns]])*self.inverse

        def visit(depth, point, word):
            if depth == len(self.free):
                entries = point.entries()
                if any(v not in (0,1) for v in entries):
                    return
                word |= mask(i for i,v in zip(self.rows,entries) if v)
                selected = list(positions(word))
                if all(sum(self.contacts[i,j] for i in selected) == v for j,v in enumerate(target)):
                    yield word
                return
            yield from visit(depth+1,point,word)
            yield from visit(depth+1,point+self.directions[depth],word|(1 << self.free[depth]))

        yield from visit(0,start,0)


def square_neighborhoods(options, boundary_size):
    for chosen in combinations(options,4):
        parents = [0]*4
        for i,j in combinations(range(4),2):
            overlap = (chosen[i]&chosen[j]).bit_count()
            if overlap > 1:
                break
            if overlap:
                parents[i] |= 1 << j
                parents[j] |= 1 << i
        else:
            if all(w.bit_count() == 2 for w in parents):
                membership = [mask(i for i,w in enumerate(chosen) if (w>>j)&1)
                              for j in range(boundary_size)]
                if all(w.bit_count() in (1,2) for w in membership):
                    yield chosen,parents,membership


def assemble(exterior, contacts, parents, membership, rows):
    boundary = contacts.nrows()
    start = 4+boundary
    result = Matrix(start+exterior.nrows(),start+exterior.nrows())

    def edge(i,j):
        result[i,j] = result[j,i] = 1

    for i,w in enumerate(parents):
        for j in positions(w):
            edge(i,j)
    for i,w in enumerate(membership):
        for j in positions(w):
            edge(4+i,j)
        for j in positions(rows[i]):
            edge(4+i,4+j)
        for j in range(exterior.nrows()):
            if contacts[i,j]:
                edge(4+i,start+j)
    for i in range(exterior.nrows()):
        for j in range(i):
            if exterior[i,j]:
                edge(start+i,start+j)
    return result


def from_contacts(exterior, contacts, degree, stats):
    n, size = contacts.nrows(), exterior.nrows()
    solver = BinaryPreimages(contacts)
    parents = [w for w in solver.solve([2]*size) if w.bit_count() == degree-2]
    if len(parents) < 4:
        return
    demands = Matrix([[2]*size]*n) - contacts - contacts*exterior
    possibilities = [list(solver.solve(row)) for row in demands.tolist()]
    if not all(possibilities):
        return
    weights = [sum(row) for row in contacts.tolist()]
    stats["parent_options"] = len(parents)
    for chosen,square,membership in square_neighborhoods(parents,n):
        options = []
        for i,words in enumerate(possibilities):
            member = membership[i]
            demands_ = [2-((member>>j)&1)-(member&square[j]).bit_count() for j in range(4)]
            degree_left = degree-member.bit_count()-weights[i]
            options.append([w for w in words if not (w>>i)&1 and w.bit_count()==degree_left
                            and all((w&c).bit_count()==d for c,d in zip(chosen,demands_))])
        if not all(options):
            continue
        order = sorted(range(n),key=lambda i:len(options[i]))
        rows = {}
        def visit(depth):
            if depth == n:
                graph = assemble(exterior,contacts,square,membership,rows)
                if is_graph(graph,degree):
                    yield graph
                return
            i = order[depth]
            for w in options[i]:
                if all(((w>>j)&1)==((v>>i)&1) for j,v in rows.items()):
                    rows[i] = w
                    yield from visit(depth+1)
                    del rows[i]
        yield from visit(0)


def lattice_ranks(exterior):
    """Remaining global Seidel ranks allowed by the opposite 55-site minor."""
    size = exterior.nrows()
    ones = Matrix([[1]*size]*size)
    positive = 4*identity(size)+exterior
    rank = nmod_mat((25*positive-3*ones).tolist(),7).rank()
    discriminant = int(28*positive.det()-3*(positive+ones).det())
    if discriminant < 0:
        return []
    allowed = []
    for r in (36,38,40,42):
        if rank > r-4:
            continue
        quotient, remainder = divmod(discriminant,7**(55-r))
        if remainder==0 and isqrt(quotient)**2==quotient:
            allowed.append(r)
    return allowed


def completions(exterior, degree, stats):
    order = 1 + degree*degree//2
    boundary = 4+4*(degree-4)
    size = order-4-boundary
    if exterior.nrows()!=size or exterior.ncols()!=size:
        raise ValueError("unexpected exterior order")
    if exterior != exterior.transpose() or any(v not in (0,1) for v in exterior.entries()):
        return
    if any(exterior[i,i] for i in range(size)):
        return
    caps = [int(sum(row))-degree+8 for row in exterior.tolist()]
    if not all(0<=v<=4 for v in caps):
        return
    h2 = sum(caps)-4*(degree-4)
    if h2 not in (0,2,4):
        return
    h = h2//2
    paths = 8-h-sum(v*(v-1)//2 for v in caps)
    if not 0<=paths<=4 or h and paths or degree==14 and paths==4:
        return
    if degree==14:
        if (3*identity(size)-exterior).rank()>41:
            return
        stats["lattice_ranks"] = lattice_ranks(exterior)
        if not stats["lattice_ranks"]:
            return
    gram = (degree-2)*identity(size)+Matrix([[2]*size]*size)-exterior-exterior*exterior
    if any(not 0<=gram[i,j]<=2-exterior[i,j] for i,j in combinations(range(size),2)):
        return
    if gram.rank()>boundary-3:
        return
    words = candidate_contacts(exterior,gram,degree)
    stats["candidate_rows"] = len(words)
    for contacts in contact_systems(words,gram,boundary):
        yield from from_contacts(exterior,contacts,degree,stats)


def control():
    from itertools import permutations
    full,_ = ternary_control_graph()
    neighbors = [{j for j in range(243) if full[i,j]} for i in range(243)]
    y = next(i for i in range(1,243) if i not in neighbors[0])
    a,b = sorted(neighbors[y]&neighbors[0])
    square = [0,a,y,b]
    boundary = sorted(set.union(*(neighbors[i] for i in square))-set(square))
    far = sorted(set(range(243))-set(square)-set(boundary))
    exterior = block(full,far,far)
    stats = {}
    out = list(completions(exterior,22,stats))
    labels = sorted(boundary,key=lambda i:mask(j for j,v in enumerate(far) if full[i,v]))
    assert len(out)==1 and stats=={"candidate_rows":76,"parent_options":4}
    assert any(out[0]==block(full,order,order) for parents in permutations(square)
               for order in [list(parents)+labels+far])
    assert not list(completions(Matrix(51,51),14,{}))
    print("Recovered the 243-vertex graph from its 163-vertex exterior alone.",stats)


if __name__ == "__main__":
    if len(sys.argv)==1:
        control()
    else:
        exterior = Matrix(json.loads(Path(sys.argv[1]).read_text()))
        graph = next(completions(exterior,14,{}),None)
        if graph is None:
            print("No completion for this exterior.")
        else:
            print(json.dumps([[int(x) for x in row] for row in graph.tolist()]))
