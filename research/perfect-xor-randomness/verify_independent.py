#!/usr/bin/env python3
"""Independent actual-message histograms and shell marginals by binomial sampling."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb


def bits(a, width):
    return tuple((a >> j) & 1 for j in range(width))


def parties(n, t):
    for k in range(t + 1):
        yield from combinations(range(n), k)


def seed_models(n, A, dims):
    # Each map is the coefficient of one cut for each local seed bit.
    # Generate full directed setup messages (dealers other than self).
    for seeds in product(*(range(1 << dim) for dim in dims)):
        cut = [[0]+[(u & row).bit_count()%2 for row in M]+[0]
               for u,M in zip(seeds,A)]
        send = {(d,i): a[i]^a[i+1] for d,a in enumerate(cut)
                for i in range(n) if d != i}
        local = [sum(a[i]^a[i+1] for a in cut)%2 for i in range(n)]
        yield seeds, send, local


def execution(x, local):
    transcript = []
    state = 0
    for bit, mask in zip(x, local):
        state ^= bit ^ mask
        transcript.append(state)
    assert transcript[-1] == sum(x)%2
    return transcript


def transcripts(n, C, models, x, ignore_setup=False):
    observed = [(d,i) for d,i in models[0][1] if d in C or i in C]
    seen_wires = [i for i in range(n-1) if i in C or i+1 in C]
    complete = Counter()
    for seed, setup, local in models:
        chain = execution(x, local)
        # The setup and chain lists have one fixed label per observed wire.
        # The n-1 final output messages carry the same bit, stored once.
        setup_view = () if ignore_setup else tuple(setup[e] for e in observed)
        key = (tuple(x[i] for i in C), tuple(seed[i] for i in C if i < len(seed)),
               setup_view, tuple(chain[i] for i in seen_wires), chain[-1])
        complete[key] += 1
    return complete


def moment_null(zs):
    # Solve by dense rational elimination in the binomial polynomial basis:
    # the last node's coefficient is fixed to one (not a barycentric formula).
    m = len(zs) - 1
    a = [[Fraction(choose(z,j)) for z in zs[:-1]]+
         [Fraction(-choose(zs[-1],j))] for j in range(m)]
    for j in range(m):
        k = next(k for k in range(j,m) if a[k][j])
        a[j],a[k] = a[k],a[j]
        z = a[j][j]
        a[j] = [entry/z for entry in a[j]]
        for i in range(m):
            if i != j:
                z = a[i][j]
                a[i] = [x-z*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a] + [Fraction(1)]


def choose(n, k):
    return comb(n,k) if 0 <= k <= n else 0


def shell_marginal(n, radius, h, ones):
    # Conditional sampling without replacement for ONE prescribed pattern.
    # Use counts of completions as an exact cross-check for small n.
    q = Fraction(1)
    left = radius
    for j in range(h):
        bit = j < ones
        q *= Fraction(left if bit else n-j-left, n-j)
        left -= bit
        if not q:
            break
    if n <= 256:
        assert q == Fraction(choose(n-h,radius-ones),choose(n,radius))
    return q


def isolate(S, m):
    # Model lower-bound decision leaves on each marked input independently.
    if len(S) <= 1:
        return [tuple()]
    j = next(j for j in range(m) if len({(x>>j)&1 for x in S})==2)
    return [((j,b),)+leaf for b in (0,1)
            for leaf in isolate([x for x in S if (x>>j)&1==b],m)]


def main():
    count = 0
    configs = [(4,1,[(1,2,4)]*2,[3]*2),
               (4,2,[(1,2,4)]*3,[3]*3),
               (5,2,[(1,2,4,8),(1,2,4,8),(1,2,4,8)],[4]*3),
               (5,2,[(1,2,4,8),(1,2,4,12)],[4]*2)]
    for n,t,A,dims in configs:
        models = tuple(seed_models(n,A,dims))
        for C in parties(n,t):
            reference = {}
            for a in range(1 << n):
                x = bits(a,n)
                key = (tuple(x[i] for i in C),sum(x)%2)
                h = transcripts(n,C,models,x)
                if key in reference:
                    assert h == reference[key]
                else:
                    reference[key] = h
                count += 1
    print(f"messages PASS: {count} full view histograms, all inputs and coalitions in four toy configurations")

    # Check legal post-setup uniformity independent of the rank implementation.
    # This synthetic control has uniform observed cuts unconditionally, but
    # their joint law with separate setup records is not the full privacy law.
    mats = ([1,2,4,8,0,16,0], [1,2,4,0,8,0,0], [1,2,4,0,0,0,8])
    models = tuple(seed_models(8,mats,[5,4,4]))
    x = (0,)*8
    y = (0,0,0,0,0,1,0,1)
    C = (4,6)  # zero-based parties 5 and 7
    assert transcripts(8,C,models,x,True) == transcripts(8,C,models,y,True)
    assert transcripts(8,C,models,x) != transcripts(8,C,models,y)
    print("messages PASS: aggregate-only versus separate-setup negative control")

    patterns = 0
    for k in range(1, 15):
        zs = [0,1]+[2*j**4 for j in range(1,k+1)]
        ns = zs[-1]
        ws = moment_null(zs)
        assert all(ws[j]*ws[j+1]<0 for j in range(len(ws)-1))
        P = sum(w for w in ws if w>0)
        Q = -sum(w for w in ws if w<0)
        assert P==Q and sum(abs(w)*z for z,w in zip(zs,ws))<=12*P
        for h in range(k+2):
            for a in range(h+1):
                diff = sum(w*shell_marginal(ns,z,h,a) for z,w in zip(zs,ws))
                assert (diff==0) == (h<=k)
                patterns += 1
    print(f"moments PASS: {patterns} signed hypergeometric checks, including first unmatched level")

    sets = 0
    for m in range(1, 5):
        for sz in range(1, min(5, 1 << m)+1):
            for words in combinations(range(1<<m),sz):
                leaves = isolate(words,m)
                assert len(leaves)==sz and max(map(len,leaves))<=sz-1
                for leaf in leaves:
                    assert sum(all((w>>j)&1 == b for j,b in leaf) for w in words)==1
                sets += 1
    print(f"isolation PASS: {sets} marked support sets, independent decision-leaf depth check")


if __name__=="__main__":
    main()
