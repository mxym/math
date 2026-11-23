# Twenty-nine combined rank-36 support constraints

At rank 36, twenty-nine additional positive-row certificates reduce the number of five-type supports passing the specified tests from 49 to **22**. Just one of those 22 omits norm 18: `{020,125,127,226,337}`. None of the surviving supports is certified to occur. The other 21 must contain actual neutral norm-18 fields. This is not an assertion that norm 18 occurs for *all* rank-36 graphs.

Here are the fourteen three-term hit sets. **Each** row must contain a selected type:
```
016 018 125
016 018 337
016 020 230
016 020 337
016 024 125
018 020 230
018 127 228
018 127 230
018 228 337
020 024 125
020 125 127
020 127 228
026 125 127
026 127 337
```
For each of those, the other nine selected types are left unrestricted. The remaining fifteen clauses, of greater cardinality, are in the [integer certificate data](rank36-joint-seed-hits.json). A clause H says that all types in H cannot vanish simultaneously; it does not place upper bounds on the number of other types.

The [native checker](rank36_joint_seed_hits.py) verifies each positive combination as a zero rational row after the original/extension rank-36 graph-site reduction. It explicitly verifies the full set of absence dependencies; U127=0 may supply N16=0 by the [norm-16 lift](exclusion.md). The signs are literal: the negative actual-Fano count is zero by [the rank-36 Fano exclusion](../rank36-no-fano.md). SCm denotes the **actual global** Hoffman population, SCM0 the original zero-class population, and SC('w',(2,34)) the averaged raw shell; these three rows are individually nonnegative. No new or auxiliary scalar-model constraints are needed in the checker.

The old original-class raw lower terms include C(3,53)≥16,371 (8,316 path marks and 8,055 disjoint six-site marks) from the [original quartic marking proof](original-site-quartic.md), and the [original norm-six floor](rank36-four-hit-sets.md) Y3≥44,804. Besides the [native graph-mark inequalities](original-site-populations.md), the actual graph-side rows used are the [U121 cap](u226-global-pressure.md), the [paired-square estimate](active-square-eight-all.md), the [N16 packing](norm16-four-good-bad.md), the [absence of N16 and N20 seed cap](norm18-triple-remaining-bridges.md), the [N16-free star cap](norm18-eleven-site-packing.md), the rank-free [N16/U127-free seed cap](norm18-label-edge-cap.md), and the [mixed discriminant cap](norm18-rank36-mixed-discriminant.md). The latter, in particular, needs all of 020,026,121 to vanish, since the norm-26 hypothesis there is raw.

Running `python rank36_joint_seed_hits.py` repeats the [previous cumulative support test](rank36_five_candidates.py) with the twenty-nine extra clauses and prints every five-type candidate. The numbers passing by support size 0 through 12 are
```
0, 0, 0, 0, 0, 22, 119, 253, 272, 163, 56, 11, 1.
```
These are counts of finite support patterns, not counts of graphs.
