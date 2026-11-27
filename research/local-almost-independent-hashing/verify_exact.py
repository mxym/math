"""Exact toy output laws and every two-query adaptive decision tree.

This is an exhaustive small structural instance, not an enumeration of
a production-size parameter choice with the theorem's long walk powers.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product


MULT = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))


def selectors(s):
    a, b = (s >> 2) & 3, (s >> 4) & 3
    return tuple((a ^ MULT[b][x]) & 1 for x in range(4))


def next_vertex(s, j):
    x, y = divmod(s, 32)
    if j < 8:
        if j < 4:
            x += (-1 if j&1 else 1)*(2*y+(j//2))
        else:
            y += (-1 if j&1 else 1)*(2*x+((j-4)//2))
    return 32*(x % 32)+y % 32


def all_state_pairs():
    states = Counter()
    terminal = Counter()
    for s in range(1024):
        for edge in range(16):
            t = next_vertex(s, edge)
            terminal[t] += 1
            states[selectors(s), selectors(t)] += 1
    assert len(terminal) == 1024 and set(terminal.values()) == {16}
    return states


def hash_table(state_pair, data):
    # Two chunks with two words each; use two different stripe bits in a
    # word, with a degenerate one-vertex inner sampler, and [I_2 | I_2].
    # Other bits in each word are unused and exactly factored out.
    l, r = state_pair
    return tuple(data[l[x]] ^ data[2+r[x]] for x in range(4))


def transcript(table, first, choices):
    v = table[first]
    j = choices[v]
    return (v,) if j < 0 else (v, j, table[j])


def worst_adaptive_checks():
    states = all_state_pairs()
    seed_count = sum(states.values())
    data = tuple(product(range(4), repeat=4))
    all_tables = data
    joint_real = Counter()
    pairs = tuple(combinations(range(4), 2))
    bad_weights = {p: 0 for p in pairs}
    checked_good = 0
    for s, multiplicity in states.items():
        table_law = Counter(hash_table(s, a) for a in data)
        for t, count in table_law.items():
            joint_real[t] += multiplicity*count
        for i, j in pairs:
            if any(mapping[i] == mapping[j] for mapping in s):
                bad_weights[i, j] += multiplicity
            else:
                law = Counter()
                for t, count in table_law.items():
                    law[t[i], t[j]] += count
                assert len(law) == 16 and set(law.values()) == {16}
                checked_good += 1
    assert sum(joint_real.values()) == seed_count*len(data)
    policies = 0
    max_tv = Fraction()
    for first in range(4):
        options = (-1,) + tuple(x for x in range(4) if x != first)
        for choices in product(options, repeat=4):
            real, ideal = Counter(), Counter()
            for t, m in joint_real.items():
                real[transcript(t, first, choices)] += m
            for t in all_tables:
                ideal[transcript(t, first, choices)] += seed_count
            total = seed_count*len(data)
            tv = Fraction(sum(abs(real[x]-ideal[x])
                              for x in real.keys() | ideal.keys()), 2*total)
            bad = Fraction(sum(bad_weights[tuple(sorted((first, j)))]
                               for j in choices if j >= 0), 4*seed_count)
            assert tv <= bad
            max_tv = max(max_tv, tv)
            policies += 1
    assert policies == 1024 and checked_good > 0 and max_tv > 0
    print(f"PASS exact toy laws: {seed_count} selector-edge keys, "
          f"{len(states)} selector classes, {seed_count*len(data)} active-data keys; "
          f"{checked_good} good class/pair checks")
    print(f"PASS exact TV for all {policies} adaptive query/stop policies; "
          f"max TV {max_tv}, below the corresponding ideal-bad bounds")
    same = ((0,)*4, (0,)*4)
    law = Counter(hash_table(same, a)[:2] for a in data)
    assert len(law) == 4 and max(law.values()) == 64
    tv_bad = Fraction(sum(abs(law[p]-16) for p in product(range(4), repeat=2)), 512)
    assert tv_bad == Fraction(3, 4)
    print("PASS negative control: shared locations give TV 3/4; "
          "good transcripts cannot be inferred from stationary marginals alone")


def polynomial_counts():
    for R in range(1, 4):
        for xs in combinations(range(4), R+1):
            values = set()
            for coefs in product(range(4), repeat=R+1):
                yy = []
                for x in xs:
                    acc = 0
                    for c in reversed(coefs):
                        acc = MULT[acc][x] ^ c
                    yy.append(acc)
                values.add(tuple(yy))
            assert len(values) == 4**(R+1)
    # Two occurrences of one digest are one random variable, not two.
    repeated = {(a ^ MULT[b][0], a ^ MULT[b][0]) for a, b in product(range(4), repeat=2)}
    assert len(repeated) == 4
    print("PASS finite polynomial evaluation: all distinct point lists through degree 3; "
          "repeated digest is not a fresh sample")


if __name__ == "__main__":
    worst_adaptive_checks()
    polynomial_counts()
