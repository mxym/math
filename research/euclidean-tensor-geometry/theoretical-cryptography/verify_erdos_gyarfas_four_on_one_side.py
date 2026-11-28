#!/usr/bin/env python3
"""Replay the exact four-on-one-side voltage certificates; standard library only."""
from itertools import combinations, combinations_with_replacement, permutations
import json
from pathlib import Path
import sys


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def shapes():
    """Enumerate support multisets, then assign each optional double to a row."""
    universe = tuple(range(4))
    pairs = tuple(combinations(universe, 2))
    supports = tuple(x for size in (2, 3, 4) for x in combinations(universe, size))
    perms = tuple(permutations(universe))
    row_sub = tuple(x for k in (2, 3, 4) for x in combinations(universe, k))
    out = {}

    def is_small_excluded(C, n):
        # An induced quotient with fewer than two rows or columns cannot have
        # degree three, since entries are at most two.
        col_sub = (j for k in range(2, n + 1) for j in combinations(range(n), k))
        for J in col_sub:
            for I in row_sub:
                if len(I) == 4 and len(J) == n:
                    continue
                if len(I) > 3 and len(J) > 3:
                    continue
                if any(sum(C[j][i] for i in I) < 3 for j in J):
                    continue
                if any(sum(C[j][i] for j in J) < 3 for i in I):
                    continue
                if len(I) != 3 or len(J) != 3 or any(C[j][i] != 1 for i in I for j in J):
                    return True
        return False

    for n in (4, 5, 6):
        C = [None] * n
        reps = set()
        for support_list in combinations_with_replacement(supports, n):
            covered = tuple(set(j for j,s in enumerate(support_list) if a in s and b in s)
                            for a,b in pairs)
            if any(len(x) > 3 for x in covered):
                continue
            forbid = [set() for _ in range(n)]
            for (a,b), js in zip(pairs, covered):
                if len(js) == 3:
                    for j in js:
                        forbid[j].update((a,b))
            options = tuple(((-1,) if len(s) >= 3 else ()) +
                            tuple(i for i in s if i not in forbid[j])
                            for j,s in enumerate(support_list))
            if not all(options):
                continue

            def doubles(j, used, d_prev):
                if j == n:
                    deg_r = [sum(c[i] for c in C) for i in universe]
                    if min(deg_r) < 3:
                        return
                    # Each remaining positive cell has an endpoint of degree 3.
                    if any(sum(c) > 3 and any(c[i] and deg_r[i] > 3 for i in universe)
                           for c in C):
                        return
                    if is_small_excluded(C, n):
                        return
                    reps.add(min("/".join(sorted("".join(str(c[i]) for i in p) for c in C))
                                 for p in perms))
                    return
                s = support_list[j]
                for i in options[j]:
                    # Equal-support columns are already indistinguishable.
                    if j and s == support_list[j - 1] and i < d_prev:
                        continue
                    if i in used:
                        continue
                    C[j] = tuple(int(k in s) + int(k == i) for k in universe)
                    doubles(j + 1, used | ({i} if i >= 0 else set()), i)
            doubles(0, set(), -1)
        out[n] = reps
    return out


def row_hnf(R,n):
    M=[list(row) for row in R if any(row)]
    k=0
    for j in range(n):
        p=next((i for i in range(k,len(M)) if M[i][j]),None)
        if p is None:continue
        M[k],M[p]=M[p],M[k]
        for i in range(k+1,len(M)):
            while M[i][j]:
                q=M[k][j]//M[i][j]
                M[k],M[i]=M[i],[a-q*b for a,b in zip(M[k],M[i])]
        if M[k][j]<0:
            M[k]=[-x for x in M[k]]
        for i in range(k):
            q=M[i][j]//M[k][j]
            M[i]=[a-q*b for a,b in zip(M[i],M[k])]
        k+=1
    require(all(not any(row) for row in M[k:]),"nonzero rows left")
    return tuple(map(tuple,M[:k]))


def contains(R,v):
    for row in R:
        j=next(i for i,x in enumerate(row) if x)
        q,rem=divmod(v[j],row[j])
        if rem:return False
        v=tuple(a-q*b for a,b in zip(v,row))
    return not any(v)


def setup(name):
    C = [tuple(map(int, c)) for c in name.split("/")]
    N = 4 + len(C)
    ms = [(i,4+j,m) for j,c in enumerate(C) for i,m in enumerate(c) if m]
    component = list(range(N))
    rank = 0
    arcs = []
    sparse = []

    def add(u, v, k):
        arcs.extend(((u, v, k, 1), (v, u, k, -1)))

    for u,v,m in ms:
        k = -1
        if component[u] == component[v]:
            k = rank
            rank += 1
        else:
            a,b = component[u],component[v]
            component = [a if x == b else x for x in component]
        add(u,v,k)
        if m == 2:
            sparse.append((k,rank))
            add(u,v,rank)
            rank += 1
    require(len(set(component)) == 1, ("disconnected",name))

    def diff(i,j):
        return tuple(int(k == i) - int(k == j) for k in range(rank))

    return N, rank, arcs, tuple(diff(i,j) for i,j in sparse)


def verify(name, table):
    N, rank, arcs, different = setup(name)

    def unpack(s):
        return tuple(tuple(map(int, row.split(","))) for row in s.split(";")) if s else ()

    cells = {unpack(s): w for s,w in table.items()}
    require(len(cells) == len(table), ("duplicate rows",name))
    require(all(all(len(r) == rank for r in R) and row_hnf(R, rank) == R for R in cells),
            ("noncanonical rows",name))
    used = {}
    terminal = set()

    def visit(R):
        if R in used:
            return used[R]
        if any(contains(R, v) for v in different):
            terminal.add(R)
            return -1
        require(R in cells, ("missing branch",name,R))
        path = cells[R]
        require(len(path) in (4,8,16) and all(type(j) is int and 0 <= j < len(arcs) for j in path),
                ("malformed path",name,R))
        succ = path[1:] + path[:1]
        require(all(arcs[i][1] == arcs[j][0] and (i ^ 1) != j for i,j in zip(path, succ)),
                ("discontinuous or backtracking path",name,R))
        prefix = [[] for _ in range(N)]
        v = [0] * rank
        for i in path:
            a,_,k,sgn = arcs[i]
            prefix[a].append(tuple(v))
            if k >= 0:
                v[k] += sgn
        require(contains(R, tuple(v)), ("not closed",name,R))
        children = set()
        for p in prefix:
            for a,b in combinations(p,2):
                v = tuple(x-y for x,y in zip(a,b))
                require(not contains(R,v), ("forced collision",name,R))
                Q = row_hnf(R + (v,), rank)
                require(R != Q, ("non-strict successor",name,R))
                children.add(Q)
        depth = max((1+visit(Q) for Q in children), default=0)
        used[R] = depth
        return depth

    depth = visit(())
    require(set(used) == set(cells), ("unused states",name))
    return len(used), len(terminal), depth


def main(data):
    require(data.get("format") == "abelian-bipartite-four-on-one-side-v1","wrong format")
    S = shapes()
    cert = data["certificates"]
    expected = {4:(8,66,24,3), 5:(17,174,55,4), 6:(6,52,11,2)}
    require(set(cert) == set.union(*S.values()), "census does not match the certificate")
    for n, A in S.items():
        replay = [verify(k, cert[k]) for k in sorted(A)]
        row = (len(A), sum(x for x,y,z in replay), sum(y for x,y,z in replay),
               max(z for x,y,z in replay))
        require(row == expected[n], ("unexpected census",n,row))
        print(f"opposite side {n}: templates/states/terminal/depth = {row}")
    print("PASS, 31 templates; 292 nonterminal states; 90 contradictions.")


if __name__ == "__main__":
    path = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).with_name(
        "erdos_gyarfas_four_on_one_side_certificate.json")
    main(json.loads(path.read_text(encoding="utf-8")))
