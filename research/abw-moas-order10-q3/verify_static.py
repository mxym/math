#!/usr/bin/env python3
"""Direct check of the static certificate against the original definitions."""

from collections import Counter
from copy import deepcopy
from itertools import combinations
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Run without -O")


def check(payload):
    assert payload["order"] == 10
    S = set(range(1, 11))
    labels = S | {0}
    arrays = payload["arrays"]
    assert [d["position"] for d in arrays] == [1, 2, 3]
    coords = [(x, y) for x in S for y in S if x != y]

    for spec in arrays:
        i = spec["position"]
        table = spec["rows"]
        assert len(table) == 10 and all(len(row) == 10 for row in table)
        for x in S:
            row = table[x-1]
            assert row[x-1] is None
            vals = [row[y-1] for y in S if y != x]
            assert all(type(a) is int for a in vals)
            need = Counter(S-{i, x})
            if x != i:
                need[0] = 1
            assert Counter(vals) == need, ("row", i, x)
        for y in S:
            vals = [table[x-1][y-1] for x in S if x != y]
            need = Counter({0: 9}) if y == i else Counter(S-{i})
            assert Counter(vals) == need, ("column", i, y)

    for left, right in combinations(arrays, 2):
        i, k = left["position"], right["position"]
        A, B = left["rows"], right["rows"]
        actual = Counter((A[x-1][y-1], B[x-1][y-1]) for x, y in coords)
        required = Counter((a, b) for a in labels-{i} for b in labels-{k}
                           if a != b and (a, b) != (k, i))
        assert len(required) == 90
        assert actual == required, ("orthogonality", i, k)


if __name__ == "__main__":
    payload = json.loads(Path(__file__).with_name("arrays_order10.json").read_text())
    check(payload)
    print("order 10: 30 rows, 30 columns, and 270 allowed ordered pair entries PASS")

    # Transpose two small outputs in one row. The row remains valid;
    # the other constraints must reject the altered certificate.
    bad = deepcopy(payload)
    first = bad["arrays"][0]["rows"][0]
    first[1], first[2] = first[2], first[1]
    try:
        check(bad)
    except AssertionError:
        print("corrupted-certificate negative control PASS")
    else:
        raise RuntimeError("checker did not reject the corrupted certificate")
