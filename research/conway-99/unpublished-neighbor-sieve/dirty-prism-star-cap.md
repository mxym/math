# A rank-free common-slot obstruction to the saturated-axis dirty prism

There is **no** root of a hypothetical Conway graph whose dirty graph has the nine edges of a triangular prism on six original axes and who has a saturated seventh axis \(e\). Combined with the [disjoint clean \(K_4,K_3\) bound](clean-k4-k3-cross-edge.md) and its four-cubic reduction, it follows that **every twelve-grid root has an incident triangle with a wing component of size at least 24**. This does not assert that a twelve-grid root exists, nor resolve the thirteen-grid shared-midpoint case or any entire rank.

The obstruction is a small exact count of common-neighbour slots. It depends only on a twelve-site induced graph and the shapes of six partitions of four objects. No horizontal-cell or remaining graph adjacency is assigned. The [standard-library checker](dirty_prism_star_cap.py) verifies the derived finite conditions over all ten sorted vertical edge triples; the largest remaining row-control arrays have sizes 23,23,32 or 5,32,32 before the pair joins.

## The twelve-site chart

Use the [horizontal-field conventions and moment identities](dirty-prism-vertical-edge-triples.md). The two equal horizontal cells opposite each index \(i\) have common column \(F_i\), are matchings, and have own value \(-1\) everywhere. The vertical cells \(V_i=C_{a_i b_i}\) have own edge counts \(m_i\), columns \(h_i=-F_j-F_k\), and
\[
 F_i^2=28,\quad F_i\cdot F_j=-7m_k,\quad
 \sum_{V_i}F_i=m_i-M,\quad \sum_{V_i}F_j=4-m_i,\qquad M=\sum_i m_i.
\]
As usual \(i,j,k\) are distinct. On \(V_i\) write a site's three field values as \((f_1,f_2,f_3)\) with own degree \(d\). Necessarily
\[
 -1\le f_i\le1,\qquad f_j,f_k\ge0,\qquad
 f_j+f_k=2-d,\qquad f_i+f_j,\ f_i+f_k\le1.
\]
The final inequalities follow because the other two vertical columns are disjoint-axis off-cell columns. A two-edge path within \(V_i\) uses both true sign flips at its center. A one-edge cell can have either a flip or a diagonal; matchings are unrestricted. The two other vertical packets see respectively \(1-f_i-f_k\) and \(1-f_i-f_j\) neighbours of this site, from the disjoint-axis formula.

For \(F_i\cdot F_j\) the six horizontal cells contribute exactly \(-4m_k\) and there is no common clean support, so the three vertical row tables must give \(\sum_{V_1\cup V_2\cup V_3} f_i f_j=-3m_k\). On the horizontal cells \(F_i^2\) contributes \(8+2(M-m_i)\): eight own sites of value \(-1\), and only zeroes or ones in the other rows with their known sums. All off-\(e\) clean cells have zero in every field; among the six \(e\)-star squares only the two at \(e a_i,e b_i\) can have nonzero \(F_i\), written \(t\). These star values lie in \(\{-1,0,1\}\) because \(F_i\ge-1\) and a disjoint vertical column equals \(-F_i\) there. They sum to zero **on each square** by pairing its zero clean column with \(F_i\). Thus the even integer
\[
 R_i=28-8-2(M-m_i)-\sum_{x\in V_1\cup V_2\cup V_3} f_i(x)^2
\]
lies between zero and eight, and there are exactly \(R_i/2\) negative entries in the two star squares at index \(i\) combined.

In each \(V_i\) the four sites have signed labels \(00,01,10,11\). To construct a necessary vertical chart enumerate its own graph \(m_i=0,1,2\) with the permissible degree-two centers, the displayed row bounds and column sums, and then the joint moments. Independent signed-parent flips and interchange of the two bits in a packet may be used to name its four coordinates: all retained conditions, including local common-parent coincidences, are invariant under this relabeling. This is not a graph automorphism, nor does it constrain the actual ordering of top and bottom cells. Between \(V_i,V_j\) enumerate all four-by-four zero-one matrices with the displayed row and column degrees. Retain the necessary common-neighbour cap for each vertex pair, counting neighbours inside the vertical twelve-set and their shared first-layer parent if they lie in the same packet and differ in one sign.

## Required capacities of the six star squares

For each pair of vertical vertices, let its *debt* be the number \(2-[x\sim y]\) minus already known common neighbours in the vertical twelve-set and among the first-layer parents. Root \(o\) sees no vertical vertex. There are two kinds of remaining sources of common neighbours:

1. Each saturated-axis star square \(C_{e a_k}\) or \(C_{e b_k}\) is anticomplete to \(V_k\) by the shared-axis clean rule. At a site with value \(t=F_k\), the two other packets each contribute \(1-t\) neighbours since their disjoint vertical columns are both \(-t\). Conversely every site of either of those two packets has exactly one contact into this star square, by its cleanness. The four sites on each participating packet are therefore partitioned into simultaneous parts of size \(1-t\). If the star has \(n\) negative rows, its common partition sizes are \(n\) doubles, \(4-2n\) singletons, and \(n\) empty parts, where \(n\in\{0,1,2\}\); the pair of stars of index \(k\) have their two \(n\)'s summing to \(R_k/2\). A part of size two contributes one internal-packet common witness for its pair. An aligned pair of parts contributes every pair in their cross Cartesian product as one common witness.
2. A site of an off-\(e\) clean square is anticomplete to the two vertical cells it shares axes with, and sees exactly one vertex in the remaining vertical cell, whose defect value there is zero. It cannot contribute any common witness between vertical vertices. For a horizontal site on the \(F_i\)-cell its own value \(f_i=-1\), and the other two values are nonnegative of sum at most one (use the disjoint column \(h_i\)). When both are zero this site sees **exactly one** vertex in each \(V_i,V_j,V_k\): in the disjoint \(V_i\) its count is \(1+h_i=1\), and in the other two it is \(h_j=h_k=1\). When one of the other values is one it sees only one vertical vertex in total, by the same formulas. Thus horizontal sites never contribute to a within-packet debt. Their cross-packet contributions all come from three-contact sites with one chosen vertex per packet.

These sources exhaust the 99 vertices: 15 at the root and first layer, 12 vertical, 24 horizontal, 24 off-\(e\) clean, and 24 star sites. Consequently the contributions of the four relevant stars must fill the debts on all six pairs **inside** each \(V_i\) exactly. Between \(V_i,V_j\), subtract the contributions of the two stars of complementary index \(k\). The residue must be a nonnegative matrix for the horizontal three-contact witnesses, so for each \(x\in V_i\) its row sum must agree with the row sum for this same \(x\) on its other face \(V_i,V_k\): each three-contact witness containing \(x\) contributes one on both faces. **Only this row condition is imposed**; the checker need not produce or enumerate any horizontal three-dimensional incidence tensor.

## The finite check and its coverage

For each pair of vertical packets, enumerate every one-square choice by partitioning each four-set with the displayed part sizes. Part labels of equal size can be permuted together, and empty parts may be omitted. The counts of distinct necessary contribution records for \(n=0,1,2\) are respectively \(24,72,18\). A record has two six-bit masks (the within-packet double pairs) and a sixteen-bit mask (the cross Cartesian products). These masks merely count contributions of one square and do not remove adjacency choices from a real graph. For the two stars enumerate both records with their required total \(n\) and reject only if their sum exceeds a debt. Store the two within-packet use vectors and the two row-sum vectors of the residual cross debt.

Join the resulting lists for \((0,1),(0,2),(1,2)\). On each vertical packet the pair-use vectors must add to the exact debt, and its two residual row-sum vectors must be equal. All that is needed in this join is tuple equality. It succeeds for **none** of the cap-vetted vertical graphs:
\[
\begin{array}{c|r|r|r}
(m_1,m_2,m_3) & \text{moment menus} & \text{vertical adjacency charts} & \text{star joins}\\\hline
(1,1,1)&88&1546&0\\
(0,2,2)&126&1464&0\\
(1,1,2)&117&210&0
\end{array}
\]
The other seven sorted triples have no moment menu; they also have a [short analytic exclusion](dirty-prism-vertical-edge-triples.md). The three nonzero counts enumerate necessary labeled records after permissible within-packet relabeling, not actual graph realizations or unlabeled graph classes. The exhaustive no-join conclusion uses neither a solver nor a timeout. That rules out the saturated-axis dirty prism.

Run `python3 dirty_prism_star_cap.py` to reproduce all ten cases and the zero joins.
