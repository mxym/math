"""Check all matched-cube partitions of the five proven N16 shores."""
from itertools import combinations

MASKS = (
    (53,77,83,106,154,166,169,212),
    (85,90,102,105,141,147,170,180),
    (58,86,89,101,149,163,172,202),
    (86,89,101,106,149,154,163,172),
    (85,90,102,105,150,153,165,170),
)
DECKS = ("8", "6+2", "4+4", "4+2+2", "2+2+2+2")
FOURS = [sum(1 << i for i in c) for c in combinations(range(8),4)]

def partitions(cols):
    def row(i):
        return sum(((col >> i) & 1) << j for j,col in enumerate(cols))
    rows = tuple(map(row, range(8)))
    assert all(x.bit_count() == 4 for x in rows + cols)
    good = []
    for pos in FOURS:
        if not pos & 1:
            continue
        for neg in FOURS:
            if not all((r & neg).bit_count() == (3 if pos >> i & 1 else 1)
                       for i, r in enumerate(rows)):
                continue
            if not all((c & pos).bit_count() == (3 if neg >> j & 1 else 1)
                       for j, c in enumerate(cols)):
                continue
            good.append((pos,neg))
    return sorted(good)

EXPECTED = [[[85,135]],[[149,177]],[[85,30],[165,120]],[[85,23],[165,212]],[[89,43],[101,77],[149,113],[169,232]]]
for deck, cols, expected in zip(DECKS, MASKS, EXPECTED, strict=True):
    found = partitions(cols)
    assert found == sorted(expected), (deck, found, expected)
    print(deck, len(found), found)
