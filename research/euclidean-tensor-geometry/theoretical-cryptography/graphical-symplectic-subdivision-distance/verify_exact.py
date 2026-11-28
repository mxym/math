"""Polynomial-basis GF(8), literal signed subgraphs and ambient supported ranks."""
from itertools import combinations, product
from math import comb
from random import Random

Q = 8
def mul(a, b):
    value = 0
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 11
    return value

M = [[mul(a, b) for b in range(Q)] for a in range(Q)]
INV = [0] + [M[a].index(1) for a in range(1, Q)]

def rank(MAT):
    a = [list(row) for row in MAT]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        candidates = [i for i in range(r, len(a)) if a[i][j]]
        if not candidates:
            continue
        i = candidates[0]
        a[i], a[r] = a[r], a[i]
        top = a[r]
        pivot = INV[top[j]]
        for i in range(r + 1, len(a)):
            if a[i][j]:
                trans = M[M[pivot][a[i][j]]]
                a[i][j:] = [x ^ trans[y] for x, y in zip(a[i][j:], top[j:])]
        r += 1
        if r == len(a):
            break
    return r

def selrank(h, cols):
    return rank([[r[j] for j in cols] for r in h])

def omega(a, b):
    m = len(a)//2
    z = 0
    for i in range(m):
        z ^= M[a[i]][b[i+m]] ^ M[a[i+m]][b[i]]
    return z

def ambient(h):
    assert rank(h) == len(h)
    assert all(omega(a, b) == 0 for a in h for b in h)

def chow(v, edges, tags):
    # Test the actual signed graph. Leaves cannot occur on its unique cycle.
    nbr = [[] for _ in range(v)]
    for i, ((x, y), s) in enumerate(zip(edges, tags)):
        if s:
            nbr[x].append((y, i))
            nbr[y].append((x, i))
    seen = set()
    for root in range(v):
        if root in seen:
            continue
        component = [root]
        seen.add(root)
        for x in component:
            for y, _ in nbr[x]:
                if y not in seen:
                    component.append(y)
                    seen.add(y)
        e = sum(len(nbr[x]) for x in component)//2
        if e >= len(component):
            if e != len(component):
                return False
            deg = {x: len(nbr[x]) for x in component}
            queue = [x for x in component if deg[x] == 1]
            active = {i for x in component for _, i in nbr[x]}
            for x in queue:
                for y, i in nbr[x]:
                    if i in active:
                        active.remove(i)
                        deg[y] -= 1
                        if deg[y] == 1:
                            queue.append(y)
            if not sum(tags[i] == 2 for i in active) % 2:
                return False
    return True

def columns(tags):
    m = len(tags)
    return [i+(s-1)*m for i, s in enumerate(tags) if s]

def check_tags(h, v, edges, cases):
    count = good = 0
    for tags in cases:
        cs = columns(tags)
        graph = chow(v, edges, tags)
        assert (selrank(h, cs) == len(cs)) == graph, tags
        count += 1
        good += graph
    return count, good

def distance(h, maximum):
    n, r = len(h[0])//2, len(h)
    visited = 0
    for k in range(1, maximum+1):
        good = 0
        for A in combinations(range(n), k):
            B = sorted(set(range(n)) - set(A))
            def pairs(I):
                return [j for i in I for j in (i, n+i)]
            logic = 2*k - selrank(h, pairs(A)) - r + selrank(h, pairs(B))
            assert logic >= 0
            good += logic > 0
            visited += 1
        if good:
            return k, good, visited
    raise AssertionError("distance not found")

BASE = list(combinations(range(4), 2))
H0 = [
    [1,0,0,1,1,0, 1,0,0,3,2,0],
    [0,1,0,1,0,1, 0,2,0,3,0,1],
    [0,0,1,0,1,1, 0,0,3,0,2,1],
    [0,0,0,0,0,0, 1,2,3,3,2,1],
]
A = [[0,1,1,1], [1,0,4,2], [1,4,0,1], [1,2,1,0]]
W = [[int(i == j) for j in range(4)] + A[i][:] for i in range(4)]
for row in W:
    row[0], row[4] = row[4], row[0]
C4 = [(0,1),(1,2),(2,3),(3,0)]
ambient(H0)
ambient(W)
assert check_tags(H0, 4, BASE, product(range(3), repeat=6)) == (729, 337)
assert check_tags(W, 4, C4, product(range(3), repeat=4)) == (81, 73)
assert distance(H0, 2) == (2, 15, 21)
print("exact: K4 729 signed selections; quotient distance 2 (15 pairs); C4 81 signed selections")

to_phys = lambda row: row[1:4]+row[5:8]
U = [to_phys([a^b for a,b in zip(W[i],W[1])]) for i in (2,3)]
R = [to_phys(W[i]) for i in (1,0)]
ambient(U)
assert distance(U, 2) == (2, 3, 6)
port_columns = [0,4]
data = 0
for tag in product(range(3), repeat=3):
    fc = [i+1+(s-1)*4 for i,s in enumerate(tag) if s]
    if len(fc) < 3:
        assert selrank(W, fc+port_columns) == len(fc)+2
    else:
        dep = port_columns[sum(s==2 for s in tag) % 2]
        other = 4-dep
        assert selrank(W, fc+[dep]) == 3 and selrank(W, fc+[other]) == 4
    data += 1
assert data == 27
print("exact: 27 path interfaces, shortened [[3,1,2]]_8, three weight-two supports")

def concat(h):
    n = len(h[0])//2
    def pack(parts):
        return [a for p in parts for a in p[:3]]+[a for p in parts for a in p[3:]]
    local = [pack([u if j==i else [0]*6 for j in range(n)])
             for i in range(n) for u in U]
    lifts = []
    for row in h:
        lifts.append(pack([[M[row[i]][x]^M[row[i+n]][z] for x,z in zip(*R)]
                           for i in range(n)]))
    return local + lifts

H1 = concat(H0)
ambient(H1)
edges = []
for i, (a, b) in enumerate(BASE):
    u = 4+2*i
    edges.extend(((a,u),(u,u+1),(u+1,b)))
def stress():
    # Every set of <=4 sites under all star assignments.
    for k in range(5):
        for sites in combinations(range(18), k):
            for signs in product((1,2), repeat=k):
                tags = [0]*18
                for i, s in zip(sites, signs):
                    tags[i] = s
                yield tags
    # All 16-column ground supports, with 16 deterministic signings each.
    rng = Random(20261128)
    for holes in combinations(range(18), 2):
        for _ in range(16):
            yield [0 if i in holes else 1+rng.getrandbits(1) for i in range(18)]
    # Each effective base sign or absence with four raw representatives:
    # absence may mean any incomplete pattern, even zero chosen sites.
    for base in product(range(3), repeat=6):
        for _ in range(4):
            tags = []
            for s in base:
                if s:
                    a, b = rng.getrandbits(1), rng.getrandbits(1)
                    tags.extend((1+a, 1+b, 1+(a^b^(s-1))))
                else:
                    a = [rng.randrange(3) for _ in range(3)]
                    a[rng.randrange(3)] = 0
                    tags.extend(a)
            yield tags

checks, _ = check_tags(H1, 16, edges, stress())
assert checks == sum(comb(18,k)*2**k for k in range(5)) + 153*16 + 729*4
d, num, visited = distance(H1, 4)
assert (d, num, visited) == (4, 135, 4047)
print(f"exact: subdivided K4, {checks} literal signed selections, 4047 supported quotients, distance 4 (135 four-site supports)")
