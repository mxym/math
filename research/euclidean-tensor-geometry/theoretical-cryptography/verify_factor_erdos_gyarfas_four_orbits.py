#!/usr/bin/env python3
"""Verify the four-orbit abelian power-of-two-cycle certificate with exact integers."""
import json
from itertools import combinations, permutations, product
from pathlib import Path

P = tuple(combinations(range(4),2))
PERMS = tuple(permutations(range(4)))
PERM_EDGES = [tuple(P.index(tuple(sorted((p[i],p[j])))) for i,j in P) for p in PERMS]


def quotient_types():
    representatives = set()
    labeled = 0
    for es in product(range(3),repeat=6):
        degree = [0]*4
        double = [0]*4
        for (a,b),m in zip(P,es):
            degree[a] += m
            degree[b] += m
            if m == 2:
                double[a] += 1
                double[b] += 1
        if any(x > 1 for x in double):
            continue
        connected = {0}
        for _ in range(3):
            for (a,b),m in zip(P,es):
                if m and (a in connected or b in connected):
                    connected.update((a,b))
        if len(connected) < 4:
            continue
        for ls in product(range(3),repeat=4):
            ds = [x+y for x,y in zip(ls,degree)]
            if min(ds) < 3:
                continue
            if any(m and ls[a] and ls[b] for (a,b),m in zip(P,es)):
                continue
            if any(m and ds[a] > 3 and ds[b] > 3 for (a,b),m in zip(P,es)):
                continue
            if any(l and d >= 3 for l,d in zip(ls,degree)):
                continue
            labeled += 1
            name = min(tuple(ls[i] for i in p)+tuple(es[i] for i in e)
                       for p,e in zip(PERMS,PERM_EDGES))
            representatives.add("".join(map(str,name)))
    assert labeled == 179
    return representatives


def normal_form(rows,n):
    # A row Hermite basis using only unimodular pair moves.
    a = [list(x) for x in rows]
    k = 0
    for j in range(n):
        i = next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None:
            continue
        a[k],a[i] = a[i],a[k]
        for i in range(k+1,len(a)):
            while a[i][j]:
                q = a[k][j]//a[i][j]
                a[k],a[i] = a[i],[x-q*y for x,y in zip(a[k],a[i])]
        if a[k][j] < 0:
            a[k] = [-x for x in a[k]]
        for i in range(k):
            q = a[i][j]//a[k][j]
            a[i] = [x-q*y for x,y in zip(a[i],a[k])]
        k += 1
    assert not any(any(row) for row in a[k:])
    return tuple(map(tuple,a[:k]))


def belongs(R,d):
    d = list(d)
    for row in R:
        j = next(i for i,x in enumerate(row) if x)
        q,rem = divmod(d[j],row[j])
        if rem:
            return False
        d = [x-q*y for x,y in zip(d,row)]
    return not any(d)


def setup(name):
    loops, edges = tuple(map(int,name[:4])),tuple(map(int,name[4:]))
    arrows, nonzero, relations = [], [], []
    n = 0
    comp = [{i} for i in range(4)]
    def arc(i,j,v,half=False):
        a = len(arrows)
        arrows.append((i,j,v,1,a if half else a+1))
        if not half:
            arrows.append((j,i,v,-1,a))
    for (i,j),e in zip(P,edges):
        if e == 0:
            continue
        C,D = [next(g for g in comp if z in g) for z in (i,j)]
        if C == D:
            v = n
            n += 1
        else:
            v = -1
            comp.remove(C)
            comp.remove(D)
            comp.append(C|D)
        arc(i,j,v)
        if e == 2:
            arc(i,j,n)
            nonzero.append(((n,1),(v,-1)))
            n += 1
    assert len(comp) == 1
    for i,l in enumerate(loops):
        if l == 1:
            arc(i,i,n,True)
            relations.append(((n,2),))
            nonzero.append(((n,1),))
            n += 1
        elif l == 2:
            arc(i,i,n)
            nonzero.append(((n,2),))
            n += 1
    def as_row(pairs):
        v = [0]*n
        for i,a in pairs:
            if i >= 0:
                v[i] += a
        return tuple(v)
    return n, arrows, [as_row(z) for z in nonzero], [as_row(z) for z in relations]


def word_data(n,arrows,word):
    S = [arrows[u] for u in word]
    assert not any(a[1] != b[0] or a[4] == u
                   for a,b,u in zip(S,S[1:]+S[:1],word[1:]+word[:1]))
    d = [0]*n
    seen = [[] for _ in range(4)]
    for i,j,k,s,r in S:
        seen[i].append(tuple(d))
        if k >= 0:
            d[k] += s
    collisions = {tuple(x-y for x,y in zip(a,b))
                  for row in seen for a,b in combinations(row,2)}
    return d,collisions


def verify(name,cells):
    n, arrows, req, seed = setup(name)
    root = normal_form(seed,n)
    visited = {}
    def check(R):
        if R in visited:
            return visited[R]
        assert R in cells
        height = 0
        assert not any(belongs(R,r) for r in req)
        word = cells[R]
        assert len(word) in (4,8,16)
        assert all(type(i) is int and 0 <= i < len(arrows) for i in word)
        total, diffs = word_data(n,arrows,word)
        assert belongs(R,total)
        for d in diffs:
            assert not belongs(R,d)
            RR = normal_form((*R,d),n)
            assert RR != R
            if not any(belongs(RR,r) for r in req):
                height = max(height, 1+check(RR))
        visited[R] = height
        return height
    height = check(root)
    assert visited.keys() == set(cells)
    return len(visited), height


def sharpness():
    # Direct arbitrary-deck short-walk check for the K4 template.
    n, arrows, req, seed = setup("0000111111")
    assert n == 3 and not req and not seed
    def closed(nstep):
        result = []
        def go(word,layer):
            if len(word) == nstep:
                if layer == arrows[word[0]][0] and arrows[word[-1]][4] != word[0]:
                    result.append(word)
                return
            for k,a in enumerate(arrows):
                if a[0] == layer and (not word or arrows[word[-1]][4] != k):
                    go(word+[k],a[1])
        for v in range(4):
            go([],v)
        return result
    for k in (4,8):
        walks = closed(k)
        assert len(walks) == {4:24,8:168}[k]
        assert all(any(word_data(n,arrows,w)[0]) for w in walks)
    word = [0,6,3,0,6,3,4,9,1,2,7,1,2,7,8,5]
    a,b = word_data(n,arrows,word)
    assert not any(a) and all(any(d) for d in b)
    # Coefficients of every walk/collision at length at most 16 lie in [-16,16].
    # Base 33 and p > 16*(1+33+33^2) keep all of these nonzero.
    W = (1,33,33*33)
    a = [sum(x*y for x,y in zip(d,W)) for d in b]
    assert a and all(0 < abs(x) <= 16*sum(W) for x in a)


def main():
    f = Path(__file__).with_name("erdos_gyarfas_four_orbit_certificate.json")
    tables = json.loads(f.read_text(encoding="utf-8"))
    reps = quotient_types()
    assert reps == tables.keys() and len(reps) == 15
    total = max_height = 0
    for name,cell in sorted(tables.items()):
        c = {tuple(map(tuple,json.loads(k))):w for k,w in cell.items()}
        ct, height = verify(name,c)
        total += ct
        max_height = max(max_height,height)
        print(name,ct,height)
    sharpness()
    assert total == 109 and max_height == 4
    print("PASS",len(reps),"quotient templates;",total,"nonterminal relation cells")


if __name__ == "__main__":
    main()
