# Eliminating 23 antipodal pairs in the complete E6 branch

**Conditional theorem.** If a 73-point six-dimensional kissing configuration contains an orientation of every axis of an E6 root system, it has at most **22 antipodal pairs**. No unrestricted upper bound for the six-dimensional kissing number follows.

Use the squared-norm-two normalization and the signed strict-blocker masks from the [24-pair exclusion](KissingE6TwentyFourPairs.md). That theorem already bounds the pair count by 23. With exactly 23 pairs the code has 13 singly represented original axes and 14 outsiders. Each outsider has at least five signed blockers; all blockers belong to the 13 opposites of those single roots. The negative graph of the outsiders joins pairs of product <−1, is triangle-free, and adjacent endpoints have disjoint masks. Every negative-edge endpoint therefore has between five and eight blockers. Outside vertices not on a negative edge initially have no such upper bound.

## Geometry needed beyond the previous bound

For fixed signed masks of sizes 5, 6 or 7, capacity is already one by the [five/six](KissingE6TwentyFivePairs.md) and [seven](KissingE6SevenBlockers.md) results. The same is true for every exact eight-mask. In the fundamental chamber, enumerate the six upward ideals of eight positive roots and the rational chamber sphere-slice outer hulls by the same multiple-high-vertex clipping construction. They account for four distinct signed-mask orbits, two of the six ideals being diagram reversals. The four sizes, in verifier order, are 17,280, 4,320, 25,920 and 270. The helper explicitly detects any overlap between the four orbits. For each chamber representative compare every generator pair under every Gram isometry of the eight roots (allowing both signs in the orthogonal complement when rank five). For the six ideals the comparison counts are respectively 600, 2400, 400, 92928, 600 and 2400. Each cosine is at least 1/2, with equality only between highest-root rays. Bilinearity and the triangle inequality give strictness for genuine outsiders as in the previous proof. Thus every exact signed mask of size five through eight has capacity one; **no containment exclusion involving an eight-mask is assumed**.

We use three conservative positive-product incompatibility tests for two particular relative chamber hulls. For actual points X,Y of squared norm two, we forbid coexistence only when the test proves X·Y>1. It suffices that any of the following be verified on rational hull generators x,y:
1. Every x·y≥1, with equality possible only if x or y is a highest-root generator. A positive combination representing a non-root outsider on each side has a strictly positive contribution from a pair of non-root generators, hence strictness.
2. For every x, either x·y≥||x||/√2 for **all** y, or x·y≥||x||·||y||/2 for **all** y; in either choice, equality is permitted only if x or y is on the highest-root ray of its chamber. The first estimate extends linearly in y to the actual Y. The second extends by the triangle inequality and ||Y||=√2. Extending in x then gives X·Y>1 for genuine outsiders.
3. The preceding row-wise test with the roles reversed.

To declare two **masks** incompatible, the verifier requires one of the three certificates for every relative chamber orientation, including the full stabilizer of the anchor mask. A failed test retains the pair, so loss of sharpness cannot create a false exclusion.

## Matching and union census

Use the rational negative-edge outer-hull test of the [previous paper](KissingE6TwentyFourPairs.md): if an edge is possible, some pair of generators in some allowed chambers must have product strictly below −1. Normalize the first endpoint to each mask type, scan all 103,680 group elements for the second, then saturate by the first mask stabilizer. Enumerate a second candidate disjoint edge within the same 13 available signed roots. Require four distinct masks, axis consistency, and no cross-edge inclusions among masks of sizes ≤7 (already proved incompatible). Require both edges to pass their negative-product tests. This leaves 577 anchored four-mask patterns. Applying the positive-product tests above to all four cross-edge pairs leaves 48 patterns.

The full automorphism group and the eight reorderings preserving the two edges reduce these to 8 classes. To canonicalize, choose one of the eight reorderings, transport its first mask to its canonical representative by every possible group element doing so, encode the remaining three signed masks, and take the least code. For each representative (A,B,C,D), its union U=A∪B∪C∪D has size **exactly 13**, so the matching fixes the entire available set of signed blockers. This permits a count of all outsiders, including isolated vertices.

No nine-root chamber ideal is carried into any of the eight sets U. This is checked using all seven upward ideals of size nine and every group element. Any larger blocker ideal contains a nine-root upward ideal (successively remove its minimal elements), so **no outsider with nine or more blockers can occur** in any of the eight matching scenarios. All remaining signed masks contained in U can now be read from the previously enumerated complete size 5–8 orbits:

* In seven classes there are only 14 possible masks, namely four of size five, eight of size six and two of size seven. Each has capacity one, and among them is an incompatible contained six/seven pair. Thus at most 13 outsiders fit.
* In the last class 41 possible masks are contained in U. Retain the four endpoints themselves and any other mask not geometrically incompatible with an endpoint by the positive-product tests. Only **9** candidates remain, all of capacity one.

Both contradict the required 14 outsiders. Therefore the negative graph has no matching of size two.

## Projective closure

As in the previous boundary theorem, at most one outsider need be removed from this triangle-free negative graph to leave no negative edges. The 13 remaining outsider axes and the 23 original paired axes give 36 projective code lines. By [Anstreicher's antipodal uniqueness theorem](https://optimization-online.org/2001/01/248/) they form a second E6 system, sharing exactly the 23 paired axes with the original. The common roots would give a simply-laced crystallographic system of rank at most six with 46 roots. This is impossible: the irreducible rank-six counts are 42, 60 and 72; lower irreducible ranks have at most 40; reducible systems of rank at most six have at most 42. This proves the stated conditional exclusion.

## Reproduction

Run the [standalone verifier](verify-kissing-e6-23-pairs.js) with Node.js, no external packages. Rational chamber vertices and Gram isometries use exact integer determinants. Group-orbit comparisons use a common generator scale of 1152; the script bounds direct products and squared-product comparisons strictly within the exact binary64 integer range. The negatives, positives, and mask counts above are rigorous inequalities and exact exhaustive counts, not numerical searches for approximate points. This result does not classify or exclude configurations with 22 pairs.
