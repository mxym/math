"""Verify the integer consequences of packing partner pairs at two triangles."""
from math import comb


def shell_bounds(prisms, grids, equal_pairs):
    six = (24948 + max(0, 7392 - 2*prisms - 4*equal_pairs)
           + 2*(20790 - 9*prisms - 36*grids))
    eight = (1398474 + 765072 + 18*prisms - 48*equal_pairs
             + 2*(831600 + 36*prisms - 2286*grids)
             + 96*(2079 - 9*grids) + 103*(8316 - 6*prisms))
    return six, eight


def feasible_counts():
    for prisms in range(852):
        for grids in range(prisms//6 + 1):
            bad = prisms - 6*grids
            bad_pairs = bad - int(bad % 3 != 0)
            good_pairs = min(15*grids, (3696-prisms)//4 + bad_pairs)
            quotient, remainder = divmod(6*grids, 231)
            if 231*comb(quotient, 2) + quotient*remainder > good_pairs:
                continue
            yield prisms, grids, good_pairs + bad_pairs


if __name__ == '__main__':
    counts = list(feasible_counts())
    assert 4*15 - comb(4, 2)*3 > 39
    assert all(13*p <= 9240 + 16*(p-6*g) for p, g, _ in counts)
    assert max(g for _, g, _ in counts) == 122
    assert min(p-6*g for p, g, _ in counts if p == 851) == 119
    values = {row: shell_bounds(*row) for row in counts}
    minima = tuple(min(v[j] for v in values.values()) for j in range(2))
    assert minima == (44328, 3724902)
    assert values[851, 122, 947] == minima
    print('Maximum grids: 122. Minimum bad prisms at P=851: 119.')
    print('Minimum lower bounds for squared norms six and eight:', *minima)
