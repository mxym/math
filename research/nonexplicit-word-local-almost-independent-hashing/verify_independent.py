#!/usr/bin/env python3
"""Independent bit enumerations for adaptive transcript and probe-support lemmas."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product


def tv(p,q):
    return sum(abs(p[x]-q[x]) for x in p.keys()|q.keys())/2


# Four possible inputs, three adaptively queried, one output bit.
# Seven invertible row sets and one deliberately deficient row set.
bases = ((1,2,4,8),(1,3,4,9),(1,2,7,8),(5,2,4,8),
         (1,2,4,15),(3,2,4,8),(1,2,12,8),(1,1,4,8))
def parity(x):
    return x.bit_count()%2


lists = list(permutations(range(4),3))
images = {(b,x): {tuple(parity(bases[b][j]&s) for j in x)
                  for s in range(16)}
          for b in range(8) for x in lists}
assert max(sum(len(images[b,x]) != 8 for b in range(8)) for x in lists) == 1
policies = good = with_bad = 0
for first in range(4):
    others = set(range(4))-{first}
    for left,right in product(sorted(others),repeat=2):
        second = (left,right)
        options = [tuple(sorted(others-{second[a]}))
                   for a,b in product(range(2),repeat=2)]
        for third in product(*options):
            def adaptive(answer):
                a = answer(first)
                j = second[a]
                b = answer(j)
                k = third[2*a+b]
                c = answer(k)
                return (first,j,k),(a,b,c)
            real, ideal = Counter(),Counter()
            for i in range(8):
                for tape in range(16):
                    x,y = adaptive(lambda j: parity(tape&bases[i][j]))
                    real[i,x,y] += F(1,128)
                for random_answers in product(range(2),repeat=3):
                    ans = iter(random_answers)
                    x,y = adaptive(lambda _: next(ans))
                    ideal[i,x,y] += F(1,64)
            badmass = F(0)
            for z,v in ideal.items():
                i,x,y = z
                if len(images[i,x]) == 8:
                    assert real[z] == v
                    good += 1
                else:
                    badmass += v
            assert tv(real,ideal) <= badmass <= F(1,8)
            r0,i0 = Counter(),Counter()
            for (_,x,y),v in real.items():
                r0[x,y] += v
            for (_,x,y),v in ideal.items():
                i0[x,y] += v
            assert tv(r0,i0) <= tv(real,ideal)
            with_bad += (badmass != 0)
            policies += 1

# Synthetic decision trees: input i first reads word a_i, then branch-dependent
# word b_i, then outputs parity. Probe locations can truly depend on earlier bits.
# Across 216 families, test static and adaptive location-pattern blocks
# and common-union support including mixed real/output uniform comparison.
tree = [(a,b,c) for a,b,c in product(range(3),repeat=3) if b != c]
tapes = list(product(range(2),repeat=3))
checks = unionchecks = 0
for spec in product(tree[:6],tree[6:12],tree[12:]):
    def evaluate(x,s):
        a,b,c = spec[x]
        u = (b,c)[s[a]]
        return frozenset({a,u}),s[a]^s[u]
    outcomes = {s:tuple(evaluate(x,s) for x in range(3)) for s in tapes}
    pat = {s:tuple(z[0] for z in ys) for s,ys in outcomes.items()}
    for q in range(1,4):
        for X in combinations(range(3),q):
            values = {s:tuple(outcomes[s][x][1] for x in X) for s in tapes}
            real = Counter()
            ideal = Counter({y:F(1,1<<q) for y in product(range(2),repeat=q)})
            for y in values.values():
                real[y] += F(1,8)
            err = tv(real,ideal)
            for p in set(pat.values()):
                block = [s for s in tapes if pat[s] == p]
                u = len(set.union(set(),*(p[x] for x in X)))
                assert len({values[s] for s in block}) <= 1<<u
                assert F(len(block),8)-err <= F(1<<u,1<<q)
                checks += 1
            for u in range(4):
                supp = {values[s] for s in tapes
                        if len(set.union(set(),*(pat[s][x] for x in X))) <= u}
                assert len(supp) <= 1<<u
                assert sum(real[y] for y in supp) <= err+F(1<<u,1<<q)
                unionchecks += 1

# Rank alone suffices without any fresh word for the second evaluation.
assert {(parity(s&3),parity(s&1)) for s in range(4)} == set(product(range(2),repeat=2))
print(f"PASS independent: {policies} adaptive policies ({with_bad} with bad mass); "
      f"{good} good transcript atoms; {checks} pattern "
      f"blocks; {unionchecks} cached-union checks; shared-word full rank")
