# A graph-wide soft norm-eighteen seed inequality

For a hypothetical SRG(99,14,1,2), let \(N_{16},N_{18}\) count both orientations of actual integral neutral fields, let \(U_{1,27}\) count actual signed-unit positive-charge-one cost-27 fields, and let \(P\) count actual triangular prisms. At every Seidel rank,
\[
 9N_{18}\le232848+42P+385N_{16}+544U_{1,27}.
\]
In particular \(P\le851\) gives the absolute constant 268,590. There is no extension average, no normalization by a residue count, and no assumed shell absence in this inequality.

We use the [saturated seed analysis](norm18-saturated-seed-cap.md), its [seven-mark exclusion](norm18-seven-mark-seed.md) in its strengthened two-absence form, and the [label-edge improvements](norm18-label-edge-cap.md). In those arguments the \(N_{16}=0\) assumption was used solely to forbid a same-seed pair of dot ten, and the \(U_{1,27}=0\) assumption gives an explicit actual witness, described below. No other shell is needed.

## Remove exactly the obstructions used at each seed

At every actual seed \((o,Q)\) work with its oriented norm-eighteen fields and six pair centers. First delete one endpoint of each still-present dot-ten pair. This uses altogether at most \(385N_{16}\) deletions by the [bound of 70 pairs per oriented difference and zero root](norm18-triple-remaining-bridges.md#unconditional-capacity-and-scalar-pressure): a norm-sixteen difference has eleven height-zero roots, and counting its two orientations doubles the unordered pairs. The remaining markings have no local dot-ten pair. Choose and fix four actual pair labels for each remaining marking. The chosen quartets are distinct by the [window theorem](exclusion.md).

The omissions of these quartets form a simple graph on six labels. For each of its still-present triangles delete one of the three fields corresponding to its edges. Such a triple shares the three complementary pair centers, has pairwise dot eight (dot ten was deleted and dot nine has at most two shared pair centers), and each actual field uses only its four chosen centers. For the latter assertion, every field needs at least one additional label beyond the three common centers, but their three additional sets are disjoint and lie in just the other three labels. A shared **star** of three actual pair labels is impossible by the [star theorem](norm18-dot8-star.md). Each other shared triple produces an actual unit \(U_{1,27}\) field by the [nonstar transfer](norm18-dot8-nonstar.md). Call these primary charges.

After removing the triangles, the omission graph is triangle-free. The direct proofs of \(m\le7\) on independent labels, \(m\le6\) if there is an actual label edge, and \(m\le4,3\) for at least two and three actual edges, respectively, no longer require any shell absence: they use only the already enforced local conditions. The exact older chart menu also now applies. The [label-edge tally](norm18-label-edge-cap.md) shows \(m+j+k\le6\) except possibly for seven independent-label markings or six markings with exactly one label edge. In either exception, the corresponding local proof explicitly constructs an actual unit \(U_{1,27}\) field: the other branches end in a literal common-neighbour contradiction. Delete one field there to achieve the inequality. Call this a secondary charge. There is at most one secondary charge at any seed.

Thus it remains to bound the number of primary and secondary charges to any one actual unit field, not the number of triples that give mere formal local coordinates.

## Recover the charged seed from the affine switch footprint

All charge witnesses have the same form
\[
 b=t_1+t_2+t_3-d_x-d_{x'}+\sum_{q\in Y}d_q,\quad
 p\in Q,\quad Y=Q-\{p\},\quad d_i=(3I-A)e_i .
\]
Here \(x,x'\) are two always-selected pair centers with common parent \(p\), so \(x-p-x'\) is a negative path in the terminal unit field \(b\). The core evaluations from the cited switches show:
* \(p\), \(x\), and \(x'\) are negative in \(b\); \(o\) is zero;
* the other parent of each of \(x,x'\) is positive in \(b\); these two parents are distinct, and the last member of \(Q\) is zero;
* the negative degree of \(p\) in \(b\) is two or three.

For the last assertion in detail, any neighbour of \(p\) outside the root, parents and six labels cannot be privately negative in any \(t_i\), since \(p\) is negative in all three and each sign shore is independent. That neighbour has no parent in \(Y\), since otherwise it is one of the six pair-center labels (or would violate the matching for the near graph). Thus its final value in \(b\) is nonnegative. The six known label values then decide the negative degree. Only \(x,x'\) are negative neighbours in a primary switch or a sole-label-edge secondary switch. In the independent-label secondary switch the universally omitted label has \(p\) as parent and gives the one extra negative neighbour. No other label touching \(p\) is negative. In the independent-label switch the other three noncommon labels all omit the shared parent \(p\), so their twice-positive sums are lowered by two and become zero.

For a fixed terminal \(b\), recover a candidate footprint by choosing a negative middle vertex \(p\) of degree \(d=2\) or 3 in the negative graph, its unordered path-end pair \(\{x,x'\}\), and the zero root \(o\sim p\). At negative \(p\) the equation gives \(2+d\) positive neighbours, hence at most \(12-2d\) choices of zero root. Given a candidate \(o\), the other parent \(q_x\) of \(x\) is forced as the second common neighbour of \(o,x\) besides \(p\); similarly for \(q_{x'}\). (If \(o,x\) are adjacent or these requirements fail, reject the footprint.) The last parent is a zero neighbour of \(o\); since \(o\) already has at least the two known positive neighbours and \(Ab_o=-2\), it has at least four negative neighbours, leaving at most eight zeros. This recovers \((o,Q)\) and the unordered chosen centers.

A footprint charges at most once. For a primary triangle, the unique positive label of \(b\) among the six is the third selected common center; the shift gives it value one, and all three other labels occur only once in the original sum and end nonpositive. This third common center misses \(p\), by the nonstar choice of the pair \(x,x'\). Thus the footprint and \(b\) recover the three common labels and hence the actual triangle of omitted edges; each edge corresponds to a unique marking. A secondary charge is chosen only once per seed. It also cannot use the same footprint as a primary: in the independent-label switch there is no positive label, and in a sole-edge switch any positive label is among the other centers used twice in the triple sum, so it must have parent \(p\) (its shifted value is \(2-|N(i)\cap Y|\)). The universally omitted label has value zero or \(-1\). This distinguishes the secondary from a primary positive label missing \(p\).

## Bound the total footprint count for a terminal unit marking

A unit \(b\) at \((1,27)\) has eight positive and nineteen negative sites, by its signed sum and squared norm. Let \(e_P,e_N\) be the actual internal edges of its two signs. Its cross degrees are \(6+d_P\) at positives and \(2+d_N\) at negatives, so \(e_N=e_P+5\). The common-neighbour budget of positive pairs gives
\[
 56-e_P\ge\sum_{x\text{ negative}}\binom{2+d_N(x)}2\ge19+4e_N,
\]
hence \(e_P\le3,\ e_N\le8\).

The negative graph has no triangle and no cycles of length four or five. Indeed add \(\sum_{i\in X}d_i\) at the vertices of such a cycle of length \(k=3,4,5\). With \(e(X)\ge k\), the new raw squared norm is at most \(27+21k+2k^2-14k-10k\), using \(b_i=-1\). Its charge is \(1+k\). For a triangle this is charge 4, cost at most 36; for a 4-cycle add the constant one to fold charge 5 to \(-4\), reducing cost by 11 to at most 36; for a 5-cycle the same fold of charge 6 to \(-3\) reduces cost by 33 to at most 29. All contradict the absolute signed-sum floors. Thus every cycle has length at least 6. With at most eight edges there can be only one such cycle: two edge-disjoint cycles use at least twelve edges; two distinct cycles sharing edges contain a three-path theta, in which the three pairwise path-length sums are at least six, requiring at least nine edges.

Let \(n_d\) count negative vertices of degree \(d\). The weighted middle-and-root footprint count before the final parent choice is \(8n_2+18n_3\). If the negative graph is a forest with at least an edge, then \(n_1\ge n_3+2\) and \(2n_2+4n_3\le14\); hence \(n_3\le3\) and \(8n_2+18n_3\le56+2n_3\le62\). (The zero-edge case contributes zero.) In the unicyclic case, \(n_1\ge n_3,\ 2n_2+4n_3\le16\), and \(n_3\le2\), since a cycle of length at least six leaves at most two other edges. Thus \(8n_2+18n_3\le64+2n_3\le68\). Including at most eight choices of final parent gives at most \(544\) footprints, and therefore at most \(544\) charges of either type, per terminal \(b\).

Finally sum the seed inequality after adding back deletions. The true incidence formulae are \(\sum m=9N_{18}\), \(\sum j=8(99\cdot84-6P)\), and \(\sum k\ge99\cdot336+6P\). Thus
\[
9N_{18}+\sum(j+k)\le6\cdot55,440+385N_{16}+544U_{1,27},
\]
which gives the claimed result. This is a soft upper bound, not a claim that the newly allowed populations are individually forced by a universal amount.
