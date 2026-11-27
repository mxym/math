#!/usr/bin/env python3
"""Check the difference conditions and independently expand the parameters."""

import json
from itertools import combinations
from math import gcd
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without -O")

H = (1, 2, 3)
D_BASE = ((1, 6), (2, 5), (3, 4))
F_BASE = ({2: 1, 3: 6, 4: 4, 5: 2},
          {1: 2, 3: 5, 4: 1, 6: 6},
          {1: 6, 2: 3, 5: 1, 6: 5})
BETA_BASE = ({2: 3, 3: 5}, {1: 4, 3: 3}, {1: 2, 2: 4})
GAMMA_BASE = ({1: 1, 2: 2, 3: 5},
              {1: 3, 2: 5, 3: 6},
              {1: 4, 2: 0, 3: 2})


def parameters(q):
    assert q >= 1 and gcd(q, 6) == 1
    mod = 7*q
    allparams = []
    for j, i in enumerate(H):
        eta = dict(zip((q*d for d in D_BASE[j]), (h for h in H if h != i)))
        f = {q*d: q*z for d, z in F_BASE[j].items()}
        f.update({d: ((i+1)*d) % mod for d in range(1, mod) if d % q})
        beta = {x: q*z for x, z in BETA_BASE[j].items()}
        gamma = {x: q*z for x, z in GAMMA_BASE[j].items()}
        allparams.append((eta, f, beta, gamma))
    return mod, allparams


def check_conditions(mod, data):
    goal = list(range(1, mod))
    for i, (eta, f, beta, gamma) in zip(H, data):
        assert sorted(eta.values()) == [k for k in H if k != i]
        assert not (eta.keys() & f.keys())
        assert sorted(eta.keys() | f.keys()) == goal
        assert sorted(list(f.values())+list(beta.values())) == goal
        assert sorted([(z-d) % mod for d, z in f.items()]
                      +list(gamma.values())) == [0]+goal
    for i, k in combinations(H, 2):
        eta_i, f_i, beta_i, gamma_i = data[i-1]
        eta_k, f_k, beta_k, gamma_k = data[k-1]
        l = 6-i-k
        assert not (eta_i.keys() & eta_k.keys())
        outer = [(f_k[d] - f_i[d]) % mod for d in f_i.keys() & f_k.keys()]
        seam = [(beta_k[l]-beta_i[l]) % mod]
        inner = [(gamma_k[x]-gamma_i[x]) % mod for x in H]
        assert sorted(outer+seam+inner) == goal


def expand(mod, data):
    def cell(i, x, y):
        if x == y:
            return None
        eta, f, beta, gamma = data[i-1]
        if y == i:
            return 0
        if x in H:
            if y in H:
                return 6-i-y if x == i else y
            return 4+(y-4+gamma[x]) % mod
        if y in H:
            return 4+(x-4+beta[y]) % mod
        d = (y-x) % mod
        if d in eta:
            return eta[d]
        return 4+(x-4+f[d]) % mod

    S = range(1, mod+4)
    return {"order": mod+3, "arrays": [
        {"position": i, "rows": [[cell(i, x, y) for y in S] for x in S]}
        for i in H
    ]}


if __name__ == "__main__":
    for q in (1, 5, 7, 11, 25, 49):
        mod, data = parameters(q)
        check_conditions(mod, data)
        print(f"q={q}, order={mod+3}: all R, C, and P difference lists PASS")
    expected = json.loads(Path(__file__).with_name("arrays_order10.json").read_text())
    assert expand(*parameters(1)) == expected
    print("all 300 entries of the expanded order-ten certificate match PASS")
