# Rootless rank-36 support checks and an oriented norm-20 target

The [rank-36 Fano theorem](../rank36-no-fano.md) gives the graph-wide equality N14=0. With the [original scalar/fixed-extension dictionary](rank36_four_hit_sets.py) and newer literal graph caps this rules out entire eight- and nine-type containments, not just small exact supports. The [machine-readable integer duals](rank36-rootless-hit-sets.json) and [exact native checker](rank36_rootless_hit_sets.py) certify 39 independent-of-symmetry necessary hitting conditions: in each listed set at least one selected signed-unit type must occur. The 39 sets are inclusion-incomparable. No numerical optimizer is required to verify them, and the assertion is not that these are all possible graph constraints.

Each certificate sums nonnegative rows with positive integer weights to a negative constant when its named types vanish. The checker verifies that the exact union of its absence hypotheses is the stated list. Besides rows of the published rank-36 engine, the available rows actually used are:

* −N14 = 0;
* [2G226+3N16 ≤ 5544+3U127](active-square-eight-all.md#literal-populations-and-the-rank-38-contradiction) and [U121 ≤ 29372](u226-global-pressure.md);
* [N18 ≤ 12320 if N16=N20=0](norm18-rank36-four-hit.md);
* [N16 ≤ 6496 if N20=0](norm16-good-triple-cube.md).

For example, one must hit {018,026,337}: even allowing all nine other types, rank 36 cannot miss all three. A logically different hit is {024,026,125}. See the JSON for the complete finite list.

After applying the published implication N16>0 ⇒ U127>0, the numbers of supports surviving **these necessary tests** at sizes 0 through 12 are
```
0, 0, 0, 0, 8, 76, 242, 375, 326, 171, 56, 11, 1.
```
In particular at most eight size-four supports remain:
```
018 020 024 026      018 020 024 121      018 020 026 125
018 020 121 125      016 018 024 127      016 018 125 127
018 020 125 127      020 026 125 228
```
This neither proves realizability of any support nor forces norm 18 at all support sizes. Among the eight, the only N18-free possibility is {020,026,125,228}.

## The actual norm-20 target

In fact whenever **016,018,024,230,337 are absent** at rank 36, the true graph has **at least 151,374 oriented neutral norm-20 fields**. Thus this applies to the N18-free four-type option, but does not itself exclude it. The [standalone exact coefficient proof](norm20_rank36_sparse_target.py) gives
```
2160255457 (N20 − 151373) ≥ 2091594937
```
on that larger seven-type face. The positive source rows are raw folded W022,W121,W226,W335,W444; Y1 and the already offset Y3; N16lift; the true original coclique lower tangent ('Ct',48); and the graph-wide Sidon tangent ('G',15000). The only other source is −61278663343 N14=0. The five omitted unit coefficients are spelled out in the checker. The scalar conversion is N20=2402 V020: this is the unrestricted graph-wide oriented neutral count, not a number of graphs or a bound on a different shell.
