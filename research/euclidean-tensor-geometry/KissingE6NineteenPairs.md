# Eliminating 19 antipodal pairs in the complete E6 branch

**Conditional theorem.** A 73-point six-dimensional kissing configuration that contains one representative of every E6 root line has at most **18 true antipodal pairs**. This does not exclude configurations with at most 18 pairs in that branch or configurations not containing the prescribed line system.

The [previous certificate](KissingE6TwentyPairs.md) gives at most 19 pairs. Assume equality. There are 17 unused signed original roots U and 18 outsiders. Each negative edge has squared-norm-two scalar product below −1; its endpoint masks are axis-disjoint. The [global blocker theorem](KissingE6GlobalMaskCapacity.md) bounds all outsider masks between 5 and 16 blockers and gives capacity one for each signed mask. A negative-edge endpoint thus has at most 12 blockers.

## Census with the initial enclosure

Use the previous chamber-hull and compatibility tests, adding all size-twelve diagram-orbits of upward ideals to the possible edge endpoints. Choose the first endpoint from a minimum endpoint type among the four endpoints. This costs no solutions: each unordered pair of disjoint edges can be reordered and both its edges can be reversed. Pair the second edge only if both its endpoint types are at least the anchor type. The rational negative test retains an edge if some relative-chamber generator pair has product strictly below −1; all cross-endpoint pairs must also pass the conservative positive compatibility tests.

Among 3,133 anchor orbits, 12,364,407 indexed patterns pass the necessary negative and combinatorial constraints. Of these, 1,524,245 pass the cross-endpoint checks. Discard endpoint labels as soon as their signed union has been obtained: this gives 187,036 indexed union masks, or **10,595** up to actual automorphisms of the root system. Complete these cores to 17 signed roots in all possible ways, never choosing two signs on one axis. There are **120,360** completed signed universes up to symmetry. The stabilizer-of-root-sum canonicalization and positive-ideal extension procedure are described in the [preceding proof](KissingE6TwentyPairs.md).

For each completed U, discard it if (i) fewer than 18 admissible masks have nonempty outer hull; (ii) a sign has fewer than two candidate blockers, contradicting the boundary exchange; or (iii) the positive compatibility graph has no 18-clique. As before, the boundary exchange is valid because any insertion of a missing original sign after deleting at most one blocker would yield 73 points with at least 20 antipodal pairs. The successive numbers eliminated are **3,005**, **103,422**, and **13,928**. Five signed universes survive this initial relaxation; they are explicitly listed and checked by the verifier.

## Sharpening the five-blocker enclosure

A genuine five-blocker mask is a star. Its canonical chamber has just one vertex outside the squared-norm-two sphere. Instead of the coarse five-mask envelope used above, apply the general rational sphere cut from the [seven-blocker proof](KissingE6SevenBlockers.md) also to this chamber. In simple-root product coordinates scaled by 1,152, the resulting generating set is

```
(0,1152,  0,  0,  0,   0)
(0,   0,  0,  0,  0,1152)
(0, 432,360,  0,  0,   0)
(0, 888,  0,  0,  0,   0)
(0, 660,  0,  0,492,   0)
(0, 696,  0,228,  0,   0)
(576,576, 0,  0,  0,   0)
```

For completeness: for each vertex of norm at most √2, take the last grid point, at a multiple of 1/96, of norm at most √2 along its segment towards the high vertex. The part removed by the cut is a convex hull of low vertices and cut points of norm at most √2. By strict convexity its only potential sphere points are norm-√2 vertices, which are retained on the cut. The high vertex and the cut points above therefore give an outer enclosure. The cut is used as a second necessary test; it need not be nested inside the first enclosure.

Rerun the mask-compatibility tests on the five remaining universes with this enclosure. Four now have no 18-clique. In the fifth, enumerate all distinct compatible mask pairs whose disjoint blocker sets and transported hulls still allow a negative edge. Exactly **34** such pairs remain. There is **no** choice of two vertex-disjoint such pairs for which every cross-endpoint pair is compatible. This eliminates the last universe and excludes a matching of size two.

## The alternative

The negative graph is triangle-free and therefore covered by at most one vertex in the absence of a two-edge matching. Removing one outsider leaves 17 independent outsider lines. Together with the 19 paired original axes, these give a 36-line projective kissing code. [Anstreicher’s antipodal uniqueness theorem](https://optimization-online.org/2001/01/248/) identifies it as a second E6 line system. Its intersection with the first has exactly 19 axes (outsider lines are not original axes), giving a simply-laced root system with 38 roots and rank at most six. No such system exists: an irreducible rank at most six has root count r(r+1) for A_r, 2r(r−1) for D_r, or 72 for E6; no sum of these numbers at total rank at most six is 38. This contradiction completes the conditional exclusion.

[Standalone Node.js verifier](verify-kissing-e6-19-pairs.js). The sphere cut and product comparisons use exact rational arithmetic or integer comparisons with verified safe bounds, switching to big integers for large squared products. The clique and matching searches deliberately err toward retaining non-realizable candidates.
