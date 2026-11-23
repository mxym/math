# A fixed triangle-contact chart admits no mod-seven rank-four trade

Let two labeled \((99,14,1,2)\) graphs agree on the triangle, its 36 wing sites, and all sixty labeled far contact words. Thus the only possibly different entries of their adjacency matrices are between far sites. **If their adjacency difference has rank at most four over \(\mathbf F_7\), they are identical.** In particular, when the wing Gram has mod-seven rank \(\ell\), the chart has at most one actual completion among graphs of mod-seven Seidel rank at most \(\ell+2\). This conclusion uses **no exterior adjacency rows**. It includes rank 36 with three seven-unit wing components (\(\ell=34\)), and rank 38 with one connected seven-unit wing (\(\ell=36\)). It proves uniqueness per specified labeled contact chart, not existence or exclusion of a whole branch.

For the application, take a nonsingular \(\ell\)-row principal sub-Gram of the common wing marks in \(M=3I-A+J/9\) modulo seven. All pairings against this basis, for every vertex, are fixed by the contact chart. Subtract the resulting common projection Gram in either graph. The two residual Grams have ranks at most two each, whence their difference (up to sign the adjacency difference) has rank at most four. This reasoning is unchanged by extra wing radical directions: we split off only a nondegenerate basis. Three seven-unit components have rank \(36-3+1=34\) by the centered Laplacian decomposition in [triangle-wing-twelve-currents.md](triangle-wing-twelve-currents.md); the one-component case similarly has rank 36.

## A small signed-minor lift

Write \(E=A'-A\). On global constants it vanishes, and on their real orthogonal complement it is seven times a difference \(P-Q\) of equal-rank orthogonal projections, since the two nonprincipal adjacency eigenvalues are \(3,-4\). Its nonzero eigenvalues are paired as \(\pm\lambda\): \(P+Q-I\) anticommutes with \(P-Q\), with square \(I-(P-Q)^2\), giving a bijection of opposite eigenspaces for \(0<|\lambda|<1\) before scaling; the endpoint multiplicities are then equal by zero trace. If its real rank were at least six, the sum of its principal six-minors would be minus the third elementary symmetric function of the positive squared eigenvalues, which is nonzero.

But **no nonsingular zero-diagonal symmetric six-by-six matrix with entries in \(\{0,\pm1\}\) has determinant divisible by 49**. The first small checker enumerates the 156 unsigned support graphs on six sites up to relabeling. In each forest component choose a spanning tree and make its edges positive by simultaneous row/column sign switching. All remaining edge signs are arbitrary; this gives 4562 signings in total, including harmless duplicates from unsigned automorphisms. An exact integer determinant checks the assertion for every one. If the full \(E\) has rank at most four modulo seven, each six-minor is divisible by \(7^2\) (in Smith form at least two diagonal factors have a seven, or the determinant vanishes). Consequently \(E\) has real rank at most four. Rank two was [proved to require a transposition](triangle-complement.md#a-rank-two-difference-is-a-transposition), impossible with all changes on the 8-regular far set: each transposed site loses 12 old neighbors, not at most eight. It remains to eliminate real rank four.

## Necessary constraints for a four-dimensional trade

Let \(w_i\) be the six-site incidence column of the far word at \(i\). Let \(P_i,N_i\) be the positive, negative positions of the \(i\)-th row of \(E\), now using \(P_i\) for a set, not a spectral projector. Their common cardinality \(k_i\le8\). The near-to-far block of the SRG equation in the two graphs gives
\[
 \sum_{p\in P_i}w_p=\sum_{n\in N_i}w_n.
\]
Indeed the near incidence is fixed and its product with the difference in far adjacency is zero. Each distinct pair of words shares at most two sites. For an active row, squaring the common nonnegative integer incidence sum gives
\[
 6k_i\ \le\ \sum_{p\in P_i,n\in N_i} w_p^t w_n\ \le\ 2k_i^2 .
\]
Thus every changed row loses at least three old edges. No two active rows of \(E\) are identical: otherwise their at least three common positive positions would be common neighbors in \(A'\), exceeding \(\mu\).

Let \(F\) denote the principal difference matrix restricted to active rows, and \(P=[F=1],N=[F=-1]\) its two signed support adjacencies. For distinct active sites \(i,j\) the word intersection has the stronger upper bound
\[
 C_{ij}=2-\max\big((P+P^2)_{ij},(N+N^2)_{ij}\big).
\]
This follows by counting in each graph the common near neighbors separately from the common changed neighbors already inside the far set, allowing for adjacency. A negative upper bound rejects. For every active row the necessary inequality \(\sum_{p\in P_i,n\in N_i}C_{pn}\ge6k_i\) is used below.

## Complete finite four-dimensional check

A nonzero principal four-minor exists by the paired spectrum. Any such principal Gram \(H\) represents the full rank-four nonsingular quotient and has signature \((2,2)\), hence positive determinant. Up to permutation and sign changes of the four **basis vectors** there are seven possible nonsingular hollow signed \(H\) with positive determinant. This is coordinate choice only: no sign changes are applied to the actual graphs in any comparison of common neighbors. The signature of an active vertex against this basis is a nonzero vector \(b\in\{0,\pm1\}^4\), with \(b^tH^{-1}b=0\). The four basis-site signatures up to sign must occur. Any two signatures satisfy \(b^tH^{-1}c\in\{0,\pm1\}\), determining their actual difference entry. A given signed signature can occur at most once because identical signatures give identical full rows.

Enumerate the pairwise compatible sets of antipodal signature lines that include the four basis lines. It suffices to consider their maximal supersets; every subconfiguration is recovered by choosing an arbitrary subset of the positive and negative signed representatives. There are at most nine lines per such superset. Require the basis lines to be occupied (either orientation allowed), the sum of the selected signed vectors to be zero (row sums of \(E\)), row weights \(6\le2k_i\le16\), the two uncolored \(\lambda/\mu\) caps, \(\operatorname{tr}F^3=0\), and the incidence-sum bound using \(C\) above. All operations use integer adjugates and determinants. Across maximal supersets, including duplicates, 11008 zero-sum occupancies become 323 after the row weights, 303 after the caps and cubic trace, and **eight** after the incidence-sum bound. Every one has 18 active sites.

It is unnecessary to search for either graph: each terminal chart has the following directly checked properties. \(P^2=N^2\). The only pairs to which one common edge can be added without immediately violating a common-neighbor bound in either \(P\) or \(N\) are the nine pairs \(i,\bar i\) with opposite signed rows. These form a perfect matching. The support graph of \(F\) contains a triangle. If \(K\) is the actual adjacency common to the two graphs within the active set (supported on the zero entries of \(F\)), monotonicity forces it to be a subset of these nine candidate edges. Outside-to-active incidences agree, so subtracting the active principal blocks of the two SRG equations gives
\[
 KF+FK= -F-(P^2-N^2)=-F .
\]
Put \(k'_i=[\,i\sim\bar i\text{ in }K\,]\). Since the rows of \(F\) at antipodes are negatives, this implies \(k'_i+k'_j=1\) along **every** nonzero \(F_{ij}\). The triangle makes those binary equations impossible. No rank-four trade survives.

The [standalone verifier](far_rank_four_trade.py) uses Python 3 and NumPy, only exact integer arithmetic, and no numerical optimization. It enumerates small signed pivot matrices and subsets of at most 18 signed lines, not 99-vertex graphs or far-adjacency charts.

**Odd-characteristic extension.** The [small-field trade proof](far-odd-trade.md) extends the gap to every odd prime and gives a singular-safe uniqueness criterion from the rank of a set of full known rows. It remains a fixed-chart result.
