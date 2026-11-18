"""Exhaust the six by six quotient of a possible rotation of all seven axes."""
from itertools import product


def completions(diagonal):
    rows = []
    for i, d in enumerate(diagonal):
        options = []
        for off in product(range(7), repeat=5):
            if sum(off) != 12-d or sum(x*x for x in off) != 36-d-d*d:
                continue
            options.append(off[:i] + (d,) + off[i:])
        rows.append(options)

    def extend(prefix):
        i = len(prefix)
        if i == 6:
            return 1
        return sum(extend(prefix + [row]) for row in rows[i]
                   if all(row[j] == old[i]
                          and row[j] + sum(x*y for x, y in zip(row, old)) == 24
                          for j, old in enumerate(prefix)))
    return extend([])


if __name__ == '__main__':
    for diagonal in ((6, 0, 0, 0, 0, 0), (4, 2, 0, 0, 0, 0), (2, 2, 2, 0, 0, 0)):
        total = completions(diagonal)
        print(diagonal, 'completions', total)
        assert total == 0
