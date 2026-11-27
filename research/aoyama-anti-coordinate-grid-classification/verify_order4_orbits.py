#!/usr/bin/env python3
"""Enumerate the coordinate-grid orbits of AG(2,4); optionally export representatives."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations, permutations, product
import json

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

N = 16
ALL = (1 << N) - 1
P = tuple(range(N))
F = tuple(range(4))
# F4 = F2[w]/(w^2+w+1), encoded 0,1,w,w+1.
T = ((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
INV = (0,1,3,2)
BITS = tuple(tuple(i for i in P if m>>i&1) for m in range(1<<N))


def mask(xs):
    return sum(1<<i for i in xs)


def direction(i,j):
    x,y = divmod(i^j,4)
    return T[y][INV[x]] if x else 4


def transform(pi, S):
    return tuple(sorted(mask(pi[i] for i in BITS[M]) for M in S))


def partitions(blocks):
    indexed = [[m for m in blocks if m>>i&1] for i in P]
    def aux(R,S):
        if not R:
            yield tuple(sorted(S))
            return
        i = (R&-R).bit_length()-1
        for b in indexed[i]:
            if R&b == b:
                yield from aux(R^b, S+(b,))
    return aux(ALL,())


def group():
    out = []
    for a,b,c,d in product(F,repeat=4):
        if T[a][d] == T[b][c]:
            continue
        for h,s in product(P,range(2)):
            f = [T[x][x] if s else x for x in F]
            pi = tuple(h^(4*(T[a][f[x]]^T[b][f[y]])+(T[c][f[x]]^T[d][f[y]]))
                       for x,y in product(F,repeat=2))
            inv = tuple(pi.index(i) for i in P)
            out.append((pi,inv))
    assert len(out) == len({pi for pi,_ in out}) == 5760
    return out


def authors_example():
    # Aoyama–Hasegawa–Hayashi–Sagara, arXiv:2608.30082v1, Example 1.
    ss = ("0011001122332323","0102231302013213","0112320330231120",
          "0120233131100322","0121323012323001")
    A = tuple(tuple(map(int,s)) for s in ss)
    D = [tuple((i&3)^T[m][i>>2] for i in P) for m in F]
    D.append(tuple(i>>2 for i in P))
    admissible = []
    for f,g in product(permutations(F),repeat=2):
        pts = [4*f[A[0][i]]+g[A[1][i]] for i in P]
        assert len(set(pts)) == 16
        if all(any(len({(s[i],ds[pts[i]]) for i in P}) == 4 for ds in D) for s in A):
            admissible.append(pts)
    assert len(admissible) == 288
    pts = admissible[0]
    parts = [tuple(sorted(mask(pts[i] for i in P if coord(i)==v) for v in F))
             for coord in (lambda i:i//4,lambda i:i%4)]
    return tuple(parts)


def run(dump):
    def dirs(q):
        return Counter(direction(i,j) for i,j in combinations(q,2))
    good = {}
    for q in combinations(P,4):
        d = dirs(q)
        if len(d) == 5:
            assert sorted(d.values()) == [1,1,1,1,2]
            good[mask(q)] = next(x for x in d if d[x]==2)
    assert len(good) == 720

    def profile(q):
        return tuple(sorted(Counter(good[i] for i in q).values(),reverse=True))

    G = group()
    parts = sorted(partitions(good))
    allparts = set(parts)
    assert len(parts) == len(allparts) == 66960
    rowmap, colmap, counts, rowprof = {},{},[],Counter()
    ordered = []
    for r in parts:
        if r in rowmap:
            continue
        stab = []
        orbit = {}
        for g,h in G:
            q = transform(g,r)
            assert q in allparts
            orbit.setdefault(q,h)  # h sends q back to r
            if q==r:
                stab.append(g)
        assert all(q not in rowmap for q in orbit)
        for q,h in orbit.items():
            rowmap[q] = (r,h)
        assert len(orbit)*len(stab)==len(G)
        ct = sorted(partitions([d for d in good if all((d&s).bit_count()==1 for s in r)]))
        U = set(ct)
        cmap = {}
        for c in ct:
            if c in cmap:
                continue
            for g in stab:
                x = transform(g,c)
                assert x in U
                cmap[x] = c
            ordered.append((r,c))
        colmap[r] = cmap
        counts.append((len(orbit),len(stab),len(ct),len(set(cmap.values()))))
        rowprof[profile(r)] += 1
    assert len(counts)==17
    assert len(rowmap)==66960
    assert sum(row_orbit*columns for row_orbit,_,columns,_ in counts) == 37909440
    assert len(ordered)==6662

    def canon(r,c):
        rep,h = rowmap[r]
        return rep,colmap[rep][transform(h,c)]

    weak_swap = [(r,c) for r,c in ordered if (r,c)==canon(c,r)]
    assert len(weak_swap)==80
    unordered = [(r,c) for r,c in ordered if (r,c)<=canon(c,r)]
    assert len(unordered)==3371
    joint = Counter(tuple(sorted((profile(r),profile(c)),reverse=True)) for r,c in unordered)

    A,B,C,D = (4,), (2,2), (2,1,1), (1,1,1,1)
    assert rowprof == {A:4,B:4,C:8,D:1}
    assert joint == {(A,A):73,(A,B):148,(A,C):402,(A,D):45,
                     (B,B):129,(B,C):827,(B,D):102,
                     (C,C):1306,(C,D):316,(D,D):23}

    ex = canon(*authors_example())
    exswap = canon(*authors_example()[::-1])
    assert ex != exswap
    assert profile(ex[0])==(4,) and profile(ex[1])==(2,1,1)
    assert ex == ((53,202,13568,51712),(833,3216,20514,40972))
    print(f"Good blocks {len(good)}; partitions {len(allparts)}; row orbits {len(counts)}")
    print(f"Profiles of row orbits: {sorted(rowprof.items(),reverse=True)}")
    print("Ordered compatible pairs 37909440; ordered orbits 6662; "
          "transpose-fixed ordered orbits 80; unoriented orbits 3371")
    for a,b in sorted(joint,reverse=True):
        print(f"{a} / {b}: {joint[(a,b)]}")
    print("Original Example 1, ordered canonical =",ex)
    print("Original Example 1, swapped canonical =",exswap)

    # Reject two deliberately invalid candidates.
    assert 15 not in good  # four collinear points
    assert (parts[0],parts[0]) not in ordered  # relative compatibility is required
    raw = json.dumps(unordered,separators=(",",":")).encode()+b"\n"
    digest = sha256(raw).hexdigest()
    assert digest == "3259c625d6551ad9b3c74811fc6e358579ea2475b392add25e5b1271a0305b8b"
    print("Unoriented JSON SHA256",digest)
    if dump:
        with open(dump,"wb") as h:
            h.write(raw)
    print("PASS direct orbit census")


if __name__=="__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--dump",help="write the complete canonical unoriented JSON list")
    run(ap.parse_args().dump)
