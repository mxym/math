# Norm-16 lifts are disjoint from the charge-two transfer budget

For an actual neutral norm-16 eigenfield, let \(P,N\) be the two independent eight-site shores, and let \(H,Z\) be the height-two and height-zero exterior sets. If \(H\) spans an edge, its unique common neighbor belongs to \(Z\). Consequently the actual graph-wide counts satisfy
\[
2G_{2,26}+3N_{16}\le 8316+3U_{1,27}.
\]
Here \(N_{16}\) is the **oriented** neutral count; each of the other two counts is for one positive charge. No rank or shell support condition is needed.

The [height-zero forest argument](../n16-zero-star-forest.md#the-cap-of-the-unique-height-two-edge) already excludes a height-one triangle cap. Suppose the edge \(hh'\) of \(H\) has cap \(p\in P\). Let \(Q,R\) be the two negative contacts of \(h,h'\), respectively. They are disjoint because \(hh'\) already has its common neighbor \(p\). Both miss the four negative contacts of \(p\), since \(hp\) and \(h'p\) already have their triangle cap. Thus \(Q\cup R\) is exactly the set of four negative sites missed by \(p\).

Let \(x\ne p\) be the other positive contact of \(h\). It misses \(h'\), because otherwise \(hh'\) would have a second common neighbor. The nonadjacent pair \(x,p\) already shares \(h\), so at most one of the four negative contacts of \(x\) can be a negative contact of \(p\). Therefore \(x\) meets at least three points of \(Q\cup R\). But the adjacent pair \(x,h\) allows at most one contact to \(Q\), and the nonadjacent pair \(x,h'\) already shares \(h\) and allows at most one to \(R\). This contradiction excludes \(p\in P\), and exchanging the shores excludes a cap in \(N\).

The [injective affine lift](exclusion.md#every-oriented-norm-16-vector-gives-a-different-unit-labeling-of-type-127) of a norm-16 marking is \(b=1_H-1_{P\cup Z}\). By the [height-two edge bound](norm16-height-two-edge.md), its positive graph has at most one edge. If there is one, the cap just located in \(Z\) has value \(-1\), not zero. Thus the lift has neither a positive induced three-vertex path nor a positive edge with a zero cap. These are the only marked outputs used by the [charge-two disjoint transfer](u226-disjoint-transfers.md). Each of the \(N_{16}\) distinct lifts contributes zero, while each remaining \(U_{1,27}\) field contributes at most three to the weighted path/edge budget. The bound follows; this use of the affine lift only claims the inequality **graph-wide**, not in an individual maximal extension.

In particular, using the [signed population identity and prism cap](u226-global-pressure.md) at rank 36 gives
\[
12N_{18}+2N_{20}+2U_{0,26}+2U_{1,25}+29U_{1,27}-17N_{16}\ \ge\ 324472.
\]
Double the identity after converting each selected population to its graph count. Bound \(18G_{2,26}\) from above by \(18\cdot4158+27(U_{1,27}-N_{16})\), and use \(G_{1,21}\le29372\). The constant is \(582\cdot2402-18\cdot4158-34\cdot29372\). This is an all-support inequality; it does not use the conditional upper bound on \(N_{18}\) or close a rank.
