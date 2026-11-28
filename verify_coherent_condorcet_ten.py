#!/usr/bin/env python3
"""Exact n=10 coherent Condorcet optimizers; uses the preceding packet checker."""
from hashlib import sha256
from itertools import combinations, permutations
from sys import argv
from verify_coherent_condorcet_maxima import (
    inv_pos, solve, check_coherent, normal_forms,
)

N = 10
CODE = (0,0,4,2,12,18,82,210,0,2,1,6,9,41,105,1,1,3,3,11,43,0,1,2,10,26,
        1,1,5,13,0,1,5,1,3,1)


def direct_witness():
    pairs = [(a,c) for a,c in combinations(range(N),2) if c > a+1]
    assert len(pairs) == len(CODE) == 36
    preference = { (a,b,c): mask>>(b-a-1)&1
                   for (a,c),mask in zip(pairs,CODE) for b in range(a+1,c) }
    assert len(preference) == 120
    test = sorted(preference.items())
    result = set()
    for p in permutations(range(N)):
        q = inv_pos(p)
        for (a,b,c), flag in test:
            if ((q[c] < min(q[a],q[b])) if flag else (q[a] > max(q[b],q[c]))):
                break
        else:
            result.add(p)
    assert len(result) == 1046
    assert sha256(str(sorted(result)).encode()).hexdigest() == (
        "ec587438071ab3725bb4270c365fc7459c8b46ea296e86aa32643c43f51257de"
    )
    return frozenset(result)


def classify(Ds):
    classes = {}
    for D in Ds:
        check_coherent(D,N,True)
        forms = list(normal_forms(D))
        assert sum(s == tuple(sorted(D)) for s in forms) == 1
        classes.setdefault(min(forms),[]).append(D)
    sizes = sorted(map(len,classes.values()))
    assert sizes == [4,4,8,8,8,8]
    dual = {}
    for a, group in classes.items():
        dual[a] = min(normal_forms(frozenset(p[::-1] for p in group[0])))
    assert all(dual[b] == a for a,b in dual.items())
    assert sum(a != b for a,b in dual.items()) == 2
    print("ordinary isomorphism classes",sizes,"; non-self-dual classes 2",flush=True)


def main():
    W = direct_witness()
    print("direct 10! rankings witness",len(W),flush=True)
    if "--witness-only" in argv:
        return
    score, Ds, nodes = solve(N, True, "--direct" in argv)
    assert score == 1046 and len(Ds) == 40 and W in Ds
    assert nodes == 414835 or "--direct" in argv
    print("exact packet traversal",score,len(Ds),nodes,flush=True)
    classify(Ds)
    print("PASS",flush=True)


if __name__ == "__main__":
    main()
