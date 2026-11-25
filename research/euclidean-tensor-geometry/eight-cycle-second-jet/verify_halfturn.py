from functools import lru_cache
from itertools import combinations, permutations

P = 1009
q = 4
c = (0, 2, 3, 11)
u = (0, 13, 0, 23)
A = {0: [(0, 0, 1)]}
D = {0: [(i, 0, u[i]) for i in range(1, q)]}
for i in range(1, q):
    j = (-i) % q
    A[i] = [(0, i, 1), (j, 0, c[i])]
    D[i] = ([] if i==2 else [(i, i, u[i]), (j, j, u[j] + 13)])

@lru_cache(None)
def trace_coefficient(row, col, k):
    # Columns use the relabeling col -> -col.
    seq = sum(zip(row, ((-x) % q for x in col)), ())
    value = 0
    for hits in combinations(range(8), k):
        walks = [(i, i, 1) for i in range(q)]
        for pos, label in enumerate(seq):
            steps = D[label] if pos in hits else A[label]
            walks = [(start, end, value * edge)
                     for start, mid, value in walks
                     for tail, end, edge in steps if mid == tail]
        value += sum(v for i, j, v in walks if i == j)
    return value % P

def rotation_orbits(words):
    out = []
    for x in sorted(words):
        orbit = [x]
        while True:
            y = orbit[-1][1:] + orbit[-1][:1]
            if y == x:
                break
            orbit.append(y)
        if min(orbit) == x and len(orbit) % 2 == 0:
            out.append(orbit)
    return out

def mat(rows, cols, degree):
    # The rotation -1 coordinate of an input basis vector is its
    # alternating orbit sum; the output coordinate is at its representative.
    return [[sum((-1)**j * trace_coefficient(r[0], w, degree)
                 for j, w in enumerate(o)) % P for o in cols] for r in rows]

def solve(A, B):
    n = len(A)
    H = [a[:] + b[:] for a, b in zip(A, B)]
    pivots = []
    for j in range(n):
        k = next(k for k in range(j, n) if H[k][j])
        H[j], H[k] = H[k], H[j]
        pivots.append(H[j][j])
        z = pow(H[j][j], -1, P)
        H[j] = [z * v % P for v in H[j]]
        for i in range(n):
            if i != j:
                z = H[i][j]
                H[i] = [(x - z*y) % P for x, y in zip(H[i], H[j])]
    return [row[n:] for row in H], pivots

def check(S):
    R = rotation_orbits(set(permutations(S)))
    C = rotation_orbits(set().union(*(set(permutations(S[:i]+(0,)+S[i+1:]))
                                       for i in range(len(S)) if S[i] != 2)))
    assert not any(any(row) for row in mat(R, R, 0))
    assert not any(any(row) for row in mat(R, R, 1))
    H = mat(C, C, 0)
    L = mat(R, C, 1)
    X, _ = solve(H, mat(C, R, 1))
    Z = [[(y-sum(a*b for a,b in zip(l,x))) % P
          for y,x in zip(row, zip(*X))] for row,l in zip(mat(R, R, 2), L)]
    I = [[int(i == j) for j in range(len(R))] for i in range(len(R))]
    assert Z == [[663, 789, 0], [759, 0, 789], [0, 759, 346]]
    _, pivots = solve([row[:2] for row in Z[:2]], [[1,0],[0,1]])
    print(S, "two retained pivots", pivots)
check((1,2,2,3))

