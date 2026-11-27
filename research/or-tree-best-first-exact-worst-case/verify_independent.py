"""Unordered tree shapes versus merge histories; literal query traversal."""
from functools import cache
from itertools import combinations


@cache
def shapes(leaves):
    if len(leaves) == 1:
        return leaves
    first, *rest = leaves
    out = []
    for s in range(len(rest)):
        for ltail in combinations(rest, s):
            left = (first,) + ltail
            right = tuple(x for x in rest if x not in ltail)
            out.extend((a, b) for a in shapes(left) for b in shapes(right))
    return tuple(out)


@cache
def label(t):
    if isinstance(t, str):
        return frozenset((t,))
    a, b = t
    return label(a) | label(b)


def visits(t, test):
    # Count the root even if the query does not pass there.
    if isinstance(t, str) or not test(label(t)):
        return 1
    return 1 + visits(t[0], test) + visits(t[1], test)


def histories(parts, test, denom, credit):
    if len(parts) == 1:
        yield parts[0]
        return
    q0, q1 = test
    def score(t):
        return (denom-credit)*q0(label(t)) + credit*q1(label(t))
    merges = [(score((a, b)), i, j, (a, b))
              for (i, a), (j, b) in combinations(enumerate(parts), 2)]
    best = min(x[0] for x in merges)
    for value, i, j, merged in merges:
        if value == best:
            new = tuple(a for k, a in enumerate(parts) if k not in (i, j)) + (merged,)
            yield from histories(new, test, denom, credit)


def main():
    total_trees = 0
    valid_histories = [0, 0]
    for n in range(3, 9):
        a = tuple(f"a{i}" for i in range((n+1)//2))
        b = tuple(f"b{i}" for i in range(n//2))
        def q0(keys):
            return any(x in keys and y in keys and
                       (x[1:] != y[1:] or int(x[1:]) >= (n-1)//2)
                       for x in a for y in b)
        def q1(keys):
            return sum(x in keys for x in a) > 1 or sum(y in keys for y in b) > 1
        # The expressions above depend only on the labels of a node,
        # not on the expected ranking of any merges on a tree.
        all_shapes = shapes(a+b)
        expected_count = 1
        for i in range(2, n):
            expected_count *= 2*i-1
        assert len(all_shapes) == expected_count
        total_trees += len(all_shapes)
        denominator = 2*n
        all_visit_pairs = tuple((visits(t, q0), visits(t, q1)) for t in all_shapes)
        assert min(x for x, _ in all_visit_pairs) == 3
        opt_expected = 3*denominator + (2*(n-2) if n >= 4 else 0)
        assert min((denominator-1)*x+y for x, y in all_visit_pairs) == opt_expected
        wtargets = (
            (0, 3, 1+2*(n//2)),
            (1, denominator*(1+2*(n//2)) - int(n % 2 == 0)*2,
                denominator*(1+2*(n//2)) - int(n % 2 == 0)*2),
        )
        for val, minima, maxima in wtargets:
            den = denominator if val else 1
            weights = (den-val, val)
            lo, hi = float("inf"), -1
            for tree in histories(a+b, (q0, q1), den, val):
                v = weights[0]*visits(tree, q0) + weights[1]*visits(tree, q1)
                lo, hi = min(lo, v), max(hi, v)
                valid_histories[val] += 1
            assert (lo, hi) == (minima, maxima)
    assert total_trees == 146598
    print(f"PASS literal visits: {total_trees} full labeled trees; "
          f"greedy histories one/two queries {valid_histories[0]}/{valid_histories[1]}")
    # A malformed query would make a satisfying descendant unreachable.
    t = (("aa", "bb"), "cc")
    assert visits(t, lambda labels: "cc" not in labels) == 1
    assert visits(t, lambda labels: "aa" in labels) == 5
    print("PASS visit-rule controls: monotone has full ancestor reachability; "
          "negation can prune true descendants")


if __name__ == "__main__":
    main()
