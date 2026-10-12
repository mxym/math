# A separate diffuse-optimum route on explicit noninteger intervals

The new [complete written note](../../notes/diffuse-fractional-cover-rounding/README.md)
supplies a route beyond the recorded triangle obstacle, under a genuine
maximum-degree/core hypothesis. It does not round an arbitrary optimum.

In the strict fractional region with maximum degree D>=3, an optimal
vertex-cover vector can be selected with every coordinate O(1/r).
The proof uses a three-complement repair and the prior finite fractional
frontier. Small triple intersections then imply small weighted triple
codegrees in the dual. A local pair-count budget and the 2/3 graph
degree test verify Kayll's matching-polytope condition, including all
higher-subset coordinates by an explicit convex mixture.

The resulting integer recovery applies for

`m/r -> c in (D-1-2/[3D(D-2)+2(D-1)],D-1]`.

For D=3 this is (24/13,2]; for D=4 it is (44/15,3]. The same conclusion
applies after o(r)-edge extraction to fractional extremizers in these
intervals. Pair intersections need not be small.

This is a restricted theorem and does not resolve the general 5.5
statement. The [source-status screen](../novelty-assessment/2026-10-07-kahn-conjecture-5-5-status-screen.md)
also does not establish that 5.5 remains open in all later literature.
The imported Kayll theorem resolves the separate 5.6 question and is
credited as prior work. Existing route records and checkers are preserved.
