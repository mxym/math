"""Local exact check for three orthogonal signed Fano configurations.

Only the Python standard library is needed.  Bits 2*i and 2*i+1 label
opposite sides of configuration i.  Vertex masks elsewhere index sites.
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def mask_of(values):
    return sum(1 << value for value in values)


def adjacent(a, b):
    return (a & b).bit_count() % 2


def site_labels(triples):
    multiple = [mask_of(2 * g + s for g, s in enumerate(t)) for t in triples]
    for g, h in combinations(range(3), 2):
        for s, t in product(range(2), repeat=2):
            pair = (1 << (2*g+s)) | (1 << (2*h+t))
            if not any(pair & v == pair for v in multiple):
                multiple.append(pair)
    single = [1 << s for s in range(6)
              for _ in range(7 - sum((v >> s) & 1 for v in multiple))]
    return multiple + single, len(multiple)


def sorted_completions(fixed, opposite):
    classes = defaultdict(list)
    for v in set(range(1, 8)).difference(fixed):
        classes[tuple(adjacent(v, w) for w in opposite)].append(v)
    return [fixed + sum(parts, ()) for parts in product(
        *(permutations(classes[k]) for k in sorted(classes)))]


def planes(group, labels, m):
    plus, minus = ([i for i, v in enumerate(labels) if v & (1 << s)]
                   for s in (2*group, 2*group+1))
    a, b = sum(i < m for i in plus), sum(i < m for i in minus)
    linear = [[0, x, y, x ^ y, z, x ^ z, y ^ z, x ^ y ^ z]
              for x, y, z in permutations(range(1, 8), 3) if x ^ y != z]
    seen, result = set(), set()
    for p in permutations(range(1, 8), a):
        if p in seen:
            continue
        seen.update(tuple(g[v] for v in p) for g in linear)
        for q in permutations(range(1, 8), b):
            if any(labels[i] & labels[j] and adjacent(v, w)
                   for i, v in zip(plus, p) for j, w in zip(minus, q)):
                continue
            # Named sites stay fixed. Canonicalize only the remaining sites
            # within each of the two sign sides.
            pfull, qfull = sorted_completions(p, q), sorted_completions(q, p)
            rows = min(tuple(mask_of(minus[k] for k, w in enumerate(right)
                                     if adjacent(v, w)) for v in left)
                       for left, right in product(pfull, qfull))
            mat = [0] * len(labels)
            for i, row in zip(plus, rows):
                mat[i] = row
                for j in bits(row):
                    mat[j] |= 1 << i
            result.add(tuple(mat))
    return result


def under_common_bound(graph):
    return all((row & graph[j]).bit_count() <= 2 - ((row >> j) & 1)
               for i, row in enumerate(graph) for j in range(i))


def pattern_key(rows, shared):
    return tuple(rows[i] & shared for i in bits(shared))


def partial_cores(labels, m, families):
    sites = [mask_of(i for i, v in enumerate(labels) if v & (3 << (2*g)))
             for g in range(3)]
    shared01, shared02, shared12 = (sites[i] & sites[j] for i,j in combinations(range(3),2))
    second, third = defaultdict(list), defaultdict(list)
    for p in families[1]:
        second[pattern_key(p, shared01)].append(p)
    for p in families[2]:
        third[pattern_key(p, shared02), pattern_key(p, shared12)].append(p)
    sides = [mask_of(j for j,v in enumerate(labels) if v & (1 << s)) for s in range(6)]
    for p in families[0]:
        for q in second[pattern_key(p, shared01)]:
            for r in third[pattern_key(p, shared02), pattern_key(q, shared12)]:
                graph = [x | y | z for x, y, z in zip(p, q, r)]
                if not under_common_bound(graph):
                    continue
                possible = True
                for i, row in enumerate(graph):
                    v = labels[i]
                    remaining = [side_degree(v,s) - (row & k).bit_count()
                                 for s,k in enumerate(sides)]
                    if min(remaining) < 0:
                        possible = False
                        break
                    # Any two multiple sites share a configuration. All their
                    # mutual incidences have already been decided.
                    if i < m and row.bit_count()+sum(remaining) > 5+3*v.bit_count():
                        possible = False
                        break
                if possible:
                    yield graph


def side_degree(label, s):
    if (label >> s) & 1:
        return 0
    return 4 if (label >> (s ^ 1)) & 1 else 1


def candidates(graph, labels):
    n = len(graph)
    groups = [sum(1 << g for g in range(3) if v & (3 << (2*g))) for v in labels]
    sides = [mask_of(j for j,v in enumerate(labels) if v & (1 << s)) for s in range(6)]
    slots = [[2-((row >> j)&1)-(row & graph[j]).bit_count() for j in range(n)] for row in graph]
    profiles = []
    # External types are the remainder W0 followed by Y0,Y1,Y2.
    for i in range(n+4):
        row = graph[i] if i < n else 0
        v = labels[i] if i < n else 0
        group = groups[i] if i < n else 0
        omitted = i-n-1 if i > n else -1
        ycounts = tuple(3*int(g != omitted and not (group & (1 << g))) for g in range(3))
        need = [side_degree(v,s)*int(s//2 != omitted) - (row & side).bit_count()
                for s,side in enumerate(sides)]
        if min(need) < 0:
            return
        assert max(need) <= 1
        avail = [j for j in range(n) if i != j and not groups[j] & group]
        options = {}

        def fill(missing, chosen):
            if not missing:
                d0 = 14-sum(ycounts)-chosen.bit_count()
                if d0 >= 0 and all((chosen & other).bit_count() <= 2-((chosen>>j)&1)
                                   for j,other in enumerate(graph) if j != i):
                    options[chosen] = (d0,*ycounts)
                return
            first = missing & -missing
            for j in avail:
                mark = labels[j]
                if not (first & mark) or mark & missing != mark:
                    continue
                if all(slots[j][k] > 0 for k in bits(chosen)):
                    fill(missing ^ mark, chosen | (1 << j))

        fill(mask_of(s for s,k in enumerate(need) if k), row)
        if not options:
            return
        profiles.append(options)
    # Compatibility of two proposed support neighborhoods only uses symmetry
    # and an upper bound on their already visible common neighbors.
    changed = True
    while changed:
        changed = False
        for i in range(n+4):
            old = profiles[i]
            keep = {}
            for a, e in old.items():
                def can_meet(j):
                    edge = (a >> j) & 1
                    return any((i >= n or ((b >> i) & 1) == edge)
                               and (a & b).bit_count() <= 2-edge for b in profiles[j])
                if all(can_meet(j) for j in range(n) if i != j):
                    keep[a] = e
            if not keep:
                return
            profiles[i] = keep
            changed |= len(old) != len(keep)
    return profiles


def last_two_cases(labels, profiles):
    n = len(labels)
    assert n == 32 and labels[:2] == [21,42]
    first, second = (next(iter(profiles[i])) for i in (0,1))
    candidates0 = profiles[n]
    if not first & 2:
        # All 22 W0 sites fit into three patterns. The two that see a also
        # see b, hence cannot be adjacent to one another.
        assert not second & 1
        assert all(list(profiles[i].values()) == [(2,0,0,0)] for i in range(2))
        assert all({v[0] for v in profiles[i].values()} == {4} for i in range(2,8))
        assert {(a & 3, (a & 252).bit_count(), e[0]) for a,e in candidates0.items()} == {
            (3,0,3), (0,1,0), (0,2,1)}
        # The six doubles give 24 incidences among the other twenty sites.
        extra = 6*4 - 20
        assert extra == 4 < 2*3
        return "nonadjacent"

    assert all(len(p) == 1 for p in profiles[:n])
    core = [next(iter(p)) for p in profiles[:n]]
    satellites = []
    for i in (0,1):
        assert list(profiles[i].values()) == [(4,0,0,0)]
        possible = [a for a in candidates0 if (a>>i)&1]
        choices = []
        for choice in combinations_with_replacement(possible,4):
            if any((a & b).bit_count() > 2 for a,b in combinations(choice,2)):
                continue
            if all(sum((a>>j)&1 for a in choice) ==
                   2-((core[i]>>j)&1)-(core[i]&core[j]).bit_count()
                   for j in range(n) if j != i):
                choices.append(choice)
        assert len(choices) == 1 and choices[0].count(3) == 1
        satellites.append([a for a in choices[0] if a != 3])
    known = [3,*satellites[0],*satellites[1]]
    assert all(candidates0[a][0] == 1 for a in known[1:])
    # Each satellite needs a second common neighbor with the other triple
    # site. The shared outside point already completes the two triples' edge.
    for i,group in enumerate(satellites):
        assert all((a & core[1-i]).bit_count() == 1 for a in group)
        assert all((a & b).bit_count() == 2 for a,b in combinations(group,2))
    survivors = 0
    for match in permutations(range(3)):
        rows = [*core,*known]
        for j,a in enumerate(known):
            for i in bits(a):
                rows[i] |= 1 << (n+j)
        for i,j in enumerate(match):
            x, y = n+1+i, n+4+j
            rows[x] |= 1 << y
            rows[y] |= 1 << x
        if not under_common_bound(rows):
            continue
        survivors += 1
        # Try a fourth signed support. Its Rayleigh quotient proves that
        # extending it by zero to all 99 sites is a global eigenvector.
        lab = labels + [0]*7
        support = [i for i,row in enumerate(rows) if (row.bit_count()-2)//3 > lab[i].bit_count()]
        assert len(support) == 14
        for positive in combinations(support,7):
            pos = set(positive)
            t = [1 if i in pos else -1 if i in support else 0 for i in range(39)]
            quad = sum(t[i]*sum(t[j] for j in bits(row)) for i,row in enumerate(rows))
            if quad != -56:
                continue
            if all(sum(t[i]*(((v>>(2*g))&1)-((v>>(2*g+1))&1))
                       for i,v in enumerate(lab)) == 0 for g in range(3)):
                break
        else:
            raise AssertionError("fourth support missing")
    assert survivors == 1
    return "adjacent"


def main():
    # Equal triple projections on two coordinates are forbidden. Modulo sign
    # changes and coordinate permutations these are all binary length-3
    # codes of minimum Hamming distance two, including the empty code.
    cases = [(), ((0,0,0),), ((0,0,0),(1,1,0)), ((0,0,0),(1,1,1)),
             ((0,0,0),(1,1,0),(0,1,1)), ((0,0,0),(1,1,0),(0,1,1),(1,0,1))]
    words = list(product(range(2),repeat=3))
    orbits = set()
    for case in cases:
        for perm in permutations(range(3)):
            for flip in words:
                orbits.add(frozenset(tuple(w[k]^flip[j] for j,k in enumerate(perm)) for w in case))
    all_codes = {frozenset(w) for k in range(9) for w in combinations(words,k)
                 if all(sum(x != y for x,y in zip(a,b)) >= 2 for a,b in combinations(w,2))}
    assert orbits == all_codes
    tally = Counter()
    for case in cases:
        labels,m = site_labels(case)
        fam = [planes(i,labels,m) for i in range(3)]
        count = 0
        passes = []
        for graph in partial_cores(labels,m,fam):
            count += 1
            rows = candidates(graph,labels)
            if rows:
                passes.append(last_two_cases(labels,rows))
        print(case, [len(f) for f in fam], count, passes, flush=True)
        tally.update(passes)
    assert tally == {"adjacent":1, "nonadjacent":1}
    print("Every three-pair case is excluded.")


if __name__ == "__main__":
    main()
