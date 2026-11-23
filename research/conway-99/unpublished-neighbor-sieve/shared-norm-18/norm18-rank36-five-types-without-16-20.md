# Rank 36 with no norm 16 or 20 needs at least five selected types

The [49 certified rank-36 must-hit sets and two support implications](rank36-four-hit-sets.md) exclude every support of cardinality at most three among the twelve selected signed-unit types. The native [exhaustive verifier](rank36_four_hit_sets.py) also checks that exactly 16 of the 495 four-element subsets survive those necessary filters and that the list in [rank36-four-controls.json](rank36-four-controls.json) has exactly those 16 distinct supports. This completeness follows from the exhaustive hit-set check, not from finding some rational controls.

Among those 16 lists, the only ones containing neither 016 nor 020 are `{018,024,026,230}` and `{018,026,125,230}`. Neither contains 228 or 337, so the new [four-type must-hit](norm18-rank36-four-hit.md) rules both out. Thus **if N16=N20=0, rank 36 requires at least five of the twelve selected unit types**. They necessarily include N18 and at least one of 228,337: the latter is the new hit; the former follows from [the original rank-44 graph-lattice coefficient identity](rank36-four-types.md#one-coefficient-identity-in-the-original-graph-lattice), which under N16=N20=0 actually yields N18≥2,092. This does not imply that five types suffice for a graph, nor that no rank-36 graph exists.

After running the native exhaustive verifier, the support filter itself is pure Python:
```python
import json
from pathlib import Path
p=Path('rank36-four-controls.json')
supports=[frozenset(map(tuple,row[0])) for row in json.loads(p.read_text())]
assert len(set(supports))==len(supports)==16
assert {s for s in supports if s.isdisjoint({(0,16),(0,20)})}=={
    frozenset({(0,18),(0,24),(0,26),(2,30)}),
    frozenset({(0,18),(0,26),(1,25),(2,30)})}
```
