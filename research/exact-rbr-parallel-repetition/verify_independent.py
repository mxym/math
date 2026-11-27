#!/usr/bin/env python3
"""Independent finite experiments: no binomial coefficients or imported DP."""
from fractions import Fraction as F
from itertools import product


def minimax_through_tree(m, r, alphabet, terminal, successors):
    # Three tests here use the complete labelled trees. Keep prefixes (not
    # just survivor counts) and every possible joint current action.
    root = ()
    table = [{root}]
    edges = {}
    for i in range(r):
        children = set()
        for history in table[-1]:
            per_action = []
            for nxt in successors(history, m, alphabet):
                assert len(nxt) == alphabet**m
                per_action.append(nxt)
                children.update(nxt)
            edges[history] = per_action
        table.append(children)

    values = {x: F(0 if terminal(x) else 1) for x in table[-1]}
    for xs in reversed(table[:-1]):
        new = {}
        for x in xs:
            costs = []
            for nxt in edges[x]:
                arr = sorted(values[y] for y in nxt)
                # For proposed tolerance e, children with needed tolerance
                # > e are excluded. Try all inclusion cut locations.
                possible = [F(1)]
                possible.extend(max(value, F(len(arr)-j-1, len(arr)))
                                for j, value in enumerate(arr))
                costs.append(min(possible))
            new[x] = max(costs)
        values = new
    return values[root]


def explicit_label_min(m, alphabet, d1, d2, shared=False):
    words = (list(product(range(alphabet), repeat=m)) if not shared
             else [(a,)*m for a in range(alphabet)])
    # Enumerate every subset of first histories to label doomed. At the
    # last layer all and only rejecting leaves should be doomed.
    assert len(words) <= 8
    full = []
    for a in words:
        accepted = sum(all(x < d1 or y < d2 for x, y in zip(a, b))
                       for b in words)
        full.append(F(accepted, len(words)))
    return min(max([F(len(words)-mask.bit_count(), len(words))]
                   + [p for j, p in enumerate(full) if (mask >> j) & 1])
               for mask in range(1 << len(words)))


def absorbed_successors(h, m, alphabet):
    yield [h + (bits,) for bits in product(range(alphabet), repeat=m)]


def alive_after(h, d, m):
    return any(all(w[j] >= di for w, di in zip(h, d)) for j in range(m))


def run_absorbed_trees():
    count = 0
    for m in range(1, 4):
        for ds in product(range(3), repeat=2):
            t = minimax_through_tree(
                m, 2, 2, lambda h: alive_after(h, ds, m), absorbed_successors)
            a = explicit_label_min(m, 2, *ds)
            assert t == a
            count += 1
    assert explicit_label_min(3, 2, 0, 1) < explicit_label_min(3, 2, 0, 1, True)
    return count


def exact_small_example():
    alphabet, m = 8, 6
    frequencies = {}
    # The next challenge is independent per coordinate. For a frozen first
    # history, conditional terminal acceptance is one completed event per
    # not-yet-event coordinate. Count first histories explicitly.
    for history in product(range(alphabet), repeat=m):
        still_unresolved = sum(x != 0 for x in history)
        value = F(1, alphabet**still_unresolved)
        frequencies[value] = frequencies.get(value, 0) + 1
    assert sum(frequencies.values()) == 262144
    # Maximal feasible intermediate sets are determined by this list of
    # exact continuation values, not by labeling only by an imposed count.
    result = min(max(v, F(sum(b for a, b in frequencies.items() if a > v), alphabet**m))
                 for v in frequencies)
    assert result == F(389, 131072) > F(1,512)
    at_target = sum(b for a, b in frequencies.items() if a > F(1,512))
    assert at_target == 778
    print(f'full first layer: {sum(frequencies.values())} histories, {at_target} forced live at (1/8)^3, exact {result}')


def finite_switching_trees():
    # Non-absorbing base states: two challenge phases and two prover
    # choices per coordinate. 0=doomed; 1=live. States may return to doomed.
    # Each fixed action can leave 0 on at most one of the two outcomes.
    m, u = 2, 2
    total = 0
    for modes in product(range(3), repeat=4):
        def next_state(s, round_, msg, challenge):
            mode = modes[2*round_+msg]
            if s == 0:
                return int(mode != 2 and challenge == mode)
            return int(mode == 2 or challenge == 1-mode)

        def states(h):
            acc = (0,)*m
            for i, record in enumerate(h):
                a, t = record
                acc = tuple(next_state(s, i, aj, tj) for s, aj, tj in zip(acc, a, t))
            return acc

        def successor(h, m, alphabet):
            all_bits = list(product(range(alphabet), repeat=m))
            for msgs in all_bits:
                yield [h+((msgs, coins),) for coins in all_bits]

        def terminal(h):
            return 0 in states(h)

        val = minimax_through_tree(m, 2, u, terminal, successor)
        # The explicit cutoffs (2,1,1) guarantee at most 1/2 for all
        # these switching games; some attain it.  No per-round action is
        # restricted to functions of their own coordinate's prior history.
        assert val <= F(1,2)
        total += 1
    return total


if __name__ == '__main__':
    exact_small_example()
    n = run_absorbed_trees()
    print(f'{n} complete two-stage uniform-bit trees, against all intermediate label subsets')
    print('negative control: shared challenge across the copies does not give the independent bound')
    b = finite_switching_trees()
    print(f'{b} joint adaptive message trees with non-absorbing individual states')
    print('PASS direct transcript and unrestricted-label checks')
