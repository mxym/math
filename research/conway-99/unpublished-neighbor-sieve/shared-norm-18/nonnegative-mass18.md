# Nonnegative complementary mass-eighteen fields: complete coefficient profiles

Let \(A\) be the adjacency matrix of a hypothetical \(\mathrm{SRG}(99,14,1,2)\). Consider **nonnegative integer** vectors
\[
 (A-3I)b=2\mathbf1,\qquad \sum_i b_i=18.
\]
This is the nonnegative part of the complementary charge-two fields; cost is \(\sum b_i^2\), with no additional scale. The full list of possible coefficient profiles is:
- eighteen singles, cost 18 (the support induces a 5-regular eighteen-set and every outside point sees two sites of it);
- one double and sixteen singles, cost 20;
- three doubles forming a triangle, and twelve singles forming a union of full cubic wing components at that triangle, cost 24;
- one coefficient 4 and fourteen singles, cost 30; exactly the 99 fields \(4e_v+1_{N(v)}\);
- nine doubles and no singles, cost 36; exactly twice each actual rook-grid indicator.

All other costs vanish in this **nonnegative** family. In particular the cost-30 nonnegative population is exactly 99, not zero. This statement does not exclude signed fields at the removed costs, assert that the one-double fields must decompose into two grids, or prove Conway nonexistence.

## Large coefficients and the double-set equations

If \(b_v\ge3\), no zero site can be adjacent to \(v\), because a zero site has neighborhood coefficient sum exactly 2. Therefore all fourteen neighbors of \(v\) are positive and the mass permits \(b_v\le4\). A coefficient 3 would require neighborhood sum 11, impossible. A coefficient 4 uses all the mass together with fourteen single neighbors. Every one of these 99 assignments is valid: an adjacent site sees the 4 and its one mate, and a nonneighbor sees exactly two singles.

Otherwise write \(D\) for the \(s\) double sites and \(S\) for the \(18-2s\) singles. Let \(H=A[D]\) denote the actual induced graph on \(D\), \(e\) its edge count and \(Q=\sum_{v\in D}\binom{\deg_H(v)}2\). Each single sees at most two doubles (its neighborhood coefficient sum is 5), and each double has coefficient sum 8 in its neighborhood. Consequently
\[
 E(D,S)=8s-4e,\qquad e\ge3s-9 .
\]
No zero vertex is a common neighbor of two doubles. If \(n_j\) counts singles having \(j\) double neighbors, the exact common-neighbor sums give
\[
 n_2=2\binom{s}{2}-e-Q,\qquad
 n_0=(18-2s)-(8s-4e)+n_2.
\]
Indeed the full pair quota on \(D\) is \(2\binom{s}{2}-e\); the internal double centers witness \(Q\), the single centers with two contacts witness \(n_2\), and zero sites contribute nothing.

We also use the ordinary induced-pair bound \(Q\le2\binom s2-e\) and the integer convex lower bounds from the actual degree sum \(2e\). If the ordinary bound is exactly saturated, every internal pair has its full common-neighbor quota inside \(H\), in particular every internal edge receives its cap in \(H\). Then each vertex has **even** internal degree, since its neighbors are paired by these local triangle caps.

## Excluding intermediate numbers of doubles

For \(s=2\) there are fourteen singles. If the two doubles \(x,y\) are nonadjacent, their eight single-neighbor sets \(U,V\) overlap in exactly two and exhaust all fourteen. Every single in \(U\setminus V\) has exactly three single neighbors and exactly one in \(U\), two in \(V\), by its pair counts with \(x,y\); no zero adjacent to a double can also meet this single. Thus these one-plus-two slots cannot overlap, and no \(U\setminus V\) vertex is adjacent to \(U\cap V\), nor vice versa with the roles switched. Each intersection vertex needs one single neighbor (it sees two doubles), so the two intersection vertices would have to be adjacent despite sharing the two doubles. If \(x,y\) are adjacent, their single-neighbor sets have size six and share just their unique cap \(c\). Any \(u\in U\setminus\{c\}\) has one neighbor in \(U\) by \(\lambda(x,u)=1\), since it does not see \(y\) and zero neighbors of \(x\) cannot see \(u\). It cannot be \(c\): the edge \(xc\) already has cap \(y\). Thus the five sites \(U\setminus\{c\}\) form a 1-regular graph, impossible.

The other exclusions use only the displayed double-set equations and integer convexity:
- \(s=4\): \(3\le e\le4\), because a four-set with five edges would contain an edge with two caps. Here \(n_0=-10+3e-Q\), negative at \(e=3\), and also at \(e=4\) since \(Q\ge4\).
- \(s=5\): \(e\ge6\). If \(e\ge7\), integer convexity gives \(Q\ge13\), with \(2\binom52-e\le13\); equality requires \(e=7\) with degree list \(3,3,3,3,2\), incompatible with the even-degree rule. So \(e=6\), and all eight singles must see two doubles by \(E(D,S)=16\). But \(Q\ge9\) at degree sum 12, so \(n_2=20-6-Q\le5\), contradiction.
- \(s=6\): \(e\ge9\). At \(e\ge10\), \(Q\ge24>30-e\), so \(e=9\). Then \(E(D,S)=12\), making all six singles see two doubles. Here \(Q\ge18\), hence \(n_2=30-9-Q\le3\), contradiction.
- \(s=7\): \(e\ge12\). The bounds \(Q\ge30\) and \(2\binom72-e\le30\) force equality and \(e=12\) with three degree-four and four degree-three vertices, again incompatible with the even-degree rule.
- \(s=8\): \(e\ge15\). Already at \(e=15\), \(Q\ge42>56-e\), impossible.

This checks all \(s\) except \(0,1,3,9\). In the three-double case \(n_0=-6+3e-Q\); for \(e=0,1,2\) it is respectively \(-6,-3,-1\), and only the triangle \(e=3\) gives zero. Each single sees exactly one of the doubles, and has three single neighbors. The pair counts with each triangle vertex force one neighbor in each physical wing (including its own mate), so the singles form a union of entire cubic components of the triangle wing. Conversely any 12-site union \(C\) gives the field \(2\,1_T+1_C\): the positive semidefinite \(G=3I-A+J/9\) has zero quadratic form on it (the weighted undirected edge sum is \(12+24+18=54\), and \(3(12+12)+18^2/9=108\)). Thus \(G(2\,1_T+1_C)=0\), which is the required equation. For \(s=9\) each double has induced degree 4, so the nine vertices make an actual rook grid by the [nine-site density equality](../../../conway-99-involution/grid-density-gap/README.md).

In the one-double case the double has eight single neighbors, comprising four of its mate pairs, and six zero neighbors comprising the other three. The remaining eight singles are outside its neighborhood, each sees precisely two of the eight first-layer singles (the common-neighbor rule with the double), and induces degree 3 among those eight outside singles. The two eight-sets are joined by a bipartite 2-regular graph. This is an exact necessary shape, not a classification of its realizations.
