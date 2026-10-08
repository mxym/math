# Literal original upper theorem

The theorem is [SharpUpperMain.lean](project/formal/Entry005/SharpUpperMain.lean), `Entry005.sharpMain : sharpMainGoal`. Its original alias is [MainTarget.lean](project/formal/Entry005/MainTarget.lean). The exact target definitions are [Targets.lean](project/formal/Entry005/Targets.lean).

For every natural dimension d ≥ 3 and compact convex body K in Euclidean d-space with nonempty interior, **for every** full-dimensional simplex S whose carrier is contained in K and whose volume is maximal among all inscribed d-simplices,

    excess(K,S) ≤ gSharp(d) · entryDefect(K)^(1/(d−1)).

`excess` is the real infimum of all t ≥ 0 for which K lies in `S.centroid + (1+t)·(S−S.centroid)`. The proof produces admissible dilations and lower bounds the infimum; it does not exploit an empty infimum. S is the caller's prescribed maximum simplex and the center is its literal arithmetic centroid. Auxiliary anchor simplices and polar simplices never replace S in the conclusion.

The actual projection volume is the Euclidean `(d−1)`-dimensional volume of the orthogonal projection onto u-perp. The actual projection body is the intersection of the corresponding support halfspaces. Write R(K)=volume(projectionBody(K))/volume(K)^(d−1). The actual pyramid is the convex hull of K embedded at height zero and the unit-height apex. The defect is

    e(K) = (d/(d+1))^d · R(pyramid(K))/R(K) − 1 − 1/(d+1).

These are actual measures and carriers, not proxy scalar data. `entryDefect` uses the ambient finrank, so the pyramid's own ratio uses dimension d+1. Defect nonnegativity is proved in the formal chain.

## Original constants

All definitions below are unchanged in [Constants.lean](project/formal/Entry005/Constants.lean):

    R0=d(d+1), b=1/[4(dR0)^d], M=1/b,
    Q=(d+1)(d+2)8^d M^(4d), L=(d−1)(M+1),
    J=(d/2)(2R0)^d [1+M+d·2^(d−1)M],
    rSharp=min(b, 1/[J(8MdL)^(d−1)]),
    eSharp=rSharp/[Q(d+1)],
    aSharp=4MdL[JQ(d+1)]^(1/(d−1)),
    gSharp=max(aSharp, (R0−1)eSharp^(−1/(d−1))).

The local theorem proves `excess ≤ aSharp·e^(1/(d−1))` for `e ≤ eSharp`; the existing coarse estimate `excess ≤ R0−1` closes the complementary branch. Zero defect is included. The smaller normalized local theorem has d ≥ 2, while the published literal target intentionally retains d ≥ 3.

The only logical axioms admitted by the complete recursive proof checks are `propext`, `Classical.choice`, and `Quot.sound`. There are no added cone-law, Minkowski, first-variation, polar geometry, cap, or retention hypotheses. This package does not prove the distinct lower truncation goal merely because that proposition is present in the unchanged target file.
