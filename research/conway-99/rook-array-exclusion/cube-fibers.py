"""Rebuild the cube gauges, run the C++17 core sieve, and check every terminal table."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb
from pathlib import Path
from triangle_pair_packing import shell_bounds
import os
import shlex
import subprocess
import tempfile

if not __debug__:
    raise RuntimeError("the verifier requires assertions")

PERMS = list(permutations(range(3)))
INV = [PERMS.index(tuple(p.index(i) for i in range(3))) for p in PERMS]
MUL = [[PERMS.index(tuple(a[b[i]] for i in range(3))) for b in PERMS] for a in PERMS]
FIBERS = [e for e in combinations(range(6), 2) if e[0]//2 != e[1]//2]
GRIDS = [c for c in combinations(range(12), 3) if len({a for i in c for a in FIBERS[i]}) == 6]
ENDS = [tuple(j for j, g in enumerate(GRIDS) if i in g) for i in range(12)]
MISSING = [(0, 1), (2, 3), (4, 5)]
STARS = [[i for i, e in enumerate(FIBERS) if a in e] for a in range(6)]
CAPS = [[i for i, e in enumerate(FIBERS) if set(e).isdisjoint(h)] for h in MISSING]
RUNGS = [[(i, j) for i, j in combinations(c, 2) if set(FIBERS[i]).isdisjoint(FIBERS[j])]
         for c in CAPS]
CORE = (1 << 36) - 1


def mask(indices):
    return sum(1 << i for i in indices)


def members(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def gauge_representatives():
    reached = {0}
    tree = []
    while len(reached) < 8:
        for i, (a, b) in enumerate(ENDS):
            if (a in reached) != (b in reached):
                tree.append(i)
                reached.update((a, b))
    free = sorted(set(range(12)) - set(tree))
    assert len(free) == 5
    actions = []
    for p in permutations(range(6)):
        if {tuple(sorted((p[a], p[b]))) for a, b in MISSING} != set(MISSING):
            continue
        fibers = [FIBERS.index(tuple(sorted((p[a], p[b])))) for a, b in FIBERS]
        grids = [GRIDS.index(tuple(sorted(fibers[i] for i in g))) for g in GRIDS]
        actions.append((fibers, grids))
    assert len(actions) == 48

    def normalized(v):
        coord = {0: 0}
        for i in tree:
            a, b = ENDS[i]
            if a in coord:
                coord[b] = MUL[v[i]][coord[a]]
            else:
                coord[a] = MUL[INV[v[i]]][coord[b]]
        return tuple(MUL[INV[coord[ENDS[i][1]]]][MUL[v[i]][coord[ENDS[i][0]]]] for i in free)

    reps, seen = [], set()
    for t in product(range(6), repeat=5):
        if t in seen:
            continue
        ident = [0]*12
        for i, value in zip(free, t):
            ident[i] = value
        orbit = set()
        for fibers, grids in actions:
            v = [0]*12
            for i, (a, b) in enumerate(ENDS):
                v[fibers[i]] = ident[i] if grids[a] < grids[b] else INV[ident[i]]
            new = normalized(v)
            for s in range(6):
                orbit.add(tuple(MUL[s][MUL[p][INV[s]]] for p in new))
        assert t in orbit and not seen.intersection(orbit)
        seen.update(orbit)
        reps.append(ident)
    assert len(reps) == 79 and len(seen) == 6**5
    return reps


def check_types_and_degrees():
    words = [mask(s) for s in STARS+CAPS]
    grids = [mask(g) for g in GRIDS]
    assert set(words) == {w for w in range(1 << 12) if all((w & g).bit_count() == 1 for g in grids)}
    c = [[2 if k == j else int(set(f).isdisjoint(h)) for j, h in enumerate(FIBERS)]
         for k, f in enumerate(FIBERS)]
    for i, edge in enumerate(FIBERS):
        # The core site sees its cap, and its other six exterior neighbors have
        # one of the two star types at the endpoints of its abstract edge.
        demands = [6+12*(j == i)-c[i][j]-sum(c[i][k]*c[k][j] for k in range(12))
                   for j in range(12)]
        group = next(s for s, inds in enumerate(CAPS) if i in inds)
        a, b = edge
        fits = [x for x in range(7) if all(demands[j] == x*(j in STARS[a]) +
                (6-x)*(j in STARS[b]) + (j in CAPS[group]) for j in range(12))]
        assert fits == [3]


def marked_graph(chart, rung_maps, alignments):
    adj = [0]*45

    def join(i, j):
        assert i != j and not adj[i] & (1 << j)
        adj[i] |= 1 << j
        adj[j] |= 1 << i

    for i in range(12):
        for a, b in combinations(range(3), 2):
            join(3*i+a, 3*i+b)
    for v, g in enumerate(GRIDS):
        for i, j in combinations(g, 2):
            src = PERMS[0 if v == ENDS[i][0] else chart[i]]
            dst = PERMS[0 if v == ENDS[j][0] else chart[j]]
            for a, b in product(range(3), repeat=2):
                if src[a] == dst[b]:
                    join(3*i+a, 3*j+b)
    for h, pairs in enumerate(RUNGS):
        for k, (i, j) in enumerate(pairs):
            for label in range(3):
                a = PERMS[alignments[h]][label] if k else label
                b = PERMS[rung_maps[2*h+k]][a]
                cap = 36+3*h+label
                join(3*i+a, 3*j+b)
                join(3*i+a, cap)
                join(3*j+b, cap)
    return adj


def all_star_tables(adj, fibers):
    # Enumerate all four-coordinate words directly; choose three per value of
    # the first coordinate. The C++ sieve instead permutes prescribed multisets.
    pairs = [(3*i+a, 3*j+b) for i,j in combinations(fibers, 2) for a,b in product(range(3), repeat=2)]
    target = [2-(adj[i]&adj[j]).bit_count() for i,j in pairs]
    assert min(target) >= 0
    slots = [mask((i,j)) for i,j in pairs]
    domains = [[] for _ in range(3)]
    for values in product(range(3), repeat=4):
        w = mask(3*i+x for i,x in zip(fibers, values))
        entries = tuple(j for j,p in enumerate(slots) if w&p == p)
        if all(target[j] for j in entries) and all((w&n).bit_count()+((w>>i)&1) <= 2
                                                    for i,n in enumerate(adj)):
            domains[values[0]].append((w,entries))
    slices = []
    for a, domain in enumerate(domains):
        current = []
        for group in combinations(domain,3):
            words = tuple(w for w,_ in group)
            if any((u&v).bit_count() > 2 for u,v in combinations(words,2)):
                continue
            counts = Counter(j for _,entries in group for j in entries)
            if any(counts[j] > cap for j,cap in enumerate(target)):
                continue
            if any(counts[j] != target[j] for j,(i,_) in enumerate(pairs) if i == 3*fibers[0]+a):
                continue
            current.append((words,counts))
        slices.append(current)
    for groups in product(*slices):
        words = sum((w for w,_ in groups), ())
        if all(sum(cnt[j] for _,cnt in groups) == cap for j,cap in enumerate(target)) and all(
                (u&v).bit_count() <= 2 for u,v in combinations(words,2)):
            yield words


def cap_can_be_completed(core, words, y):
    demand = [[2-((w>>i)&1)-(w&row).bit_count() for i,row in enumerate(core)] for w in words]
    assert min(min(row) for row in demand) >= 0
    saturated = [mask(i for i,n in enumerate(row) if n == 0) for row in demand]
    valid = [j for j,w in enumerate(words) if j != y and (w&words[y]).bit_count() <= 1 and
             not (w&saturated[y] or words[y]&saturated[j])]
    cols = [mask(j for j in valid if (words[j]>>i)&1) for i in range(36)]

    def search(needs, candidates):
        live = [i for i,n in enumerate(needs) if n]
        if not live:
            return True
        i = min(live, key=lambda k: (cols[k]&candidates).bit_count()-needs[k])
        options = cols[i]&candidates
        for chosen in combinations(members(options), needs[i]):
            new = needs.copy()
            available = candidates & ~options
            for j in chosen:
                for k in members(words[j]):
                    new[k] -= 1
                    if new[k] == 0:
                        available &= ~cols[k]
            if min(new) >= 0 and search(new,available):
                return True
        return False
    return search(demand[y],mask(valid))


def check_global_counts():
    possible = {}
    for p in range(852):
        for g in range(p//6+1):
            bad = p-6*g
            h = bad-int(bad%3 != 0)
            good_pairs = min(15*g,(3696-p+2*h)//4)
            q,r = divmod(6*g,231)
            if 231*comb(q,2)+q*r <= good_pairs:
                possible[p,g] = shell_bounds(p,g,h+good_pairs)
    assert max(g for p,g in possible) == 120
    assert min(p-6*g for p,g in possible if p==851) == 131
    assert tuple(map(min,zip(*possible.values()))) == possible[851,120] == (44636,3737742)


def run():
    check_types_and_degrees()
    check_global_counts()
    gauges = gauge_representatives()
    lines = [str(len(gauges))] + [' '.join(map(str,row)) for row in [*FIBERS,*ENDS,*gauges]]
    src = Path(__file__).with_suffix('.cpp')
    with tempfile.TemporaryDirectory() as directory:
        prog = Path(directory)/'check'
        subprocess.run([*shlex.split(os.environ.get('CXX','c++')),'-O2','-std=c++17',
                        str(src),'-o',str(prog)], check=True)
        result = subprocess.run([str(prog)],input='\n'.join(lines)+'\n',text=True,
                                stdout=subprocess.PIPE,check=True)
    survivors = 0
    for line in result.stdout.splitlines():
        row = list(map(int,line.split()))
        assert len(row) == 10
        adj = marked_graph(gauges[row[0]],row[1:7],row[7:])
        core = [w&CORE for w in adj[:36]]
        words = [w&CORE for w in adj[36:]]
        for fibers in STARS:
            tables = list(all_star_tables(adj,fibers))
            assert len(tables) == 1
            words.extend(tables[0])
        assert len(set(words)) == len(words) == 63
        for i in range(36):
            assert core[i].bit_count()+sum((w>>i)&1 for w in words) == 14
            for j in range(i):
                assert (core[i]&core[j]).bit_count()+sum((w>>i)&(w>>j)&1 for w in words) == 2-((core[i]>>j)&1)
        assert any(not cap_can_be_completed(core,words,y) for y in range(9))
        survivors += 1
    assert survivors == 15
    print('Terminal labeled tables with an impossible cap neighborhood:', survivors)


if __name__ == '__main__':
    run()
