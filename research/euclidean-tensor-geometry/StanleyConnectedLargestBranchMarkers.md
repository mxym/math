# Connected largest-branch markers on an arbitrary heavy core

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

[The single-marker theorem](StanleyLargestBranchMarker.md) can be extended to several identical markers. In particular two adjacent marked blocks suffice without a linear-independence test, even though their profiles are identical and their locations are not supplied to the reconstruction.

**Theorem.** Graft rooted blocks onto a tree core of \(q\) vertices, as in the single-marker theorem, at off-root branch bound \(h\). Suppose that:

- Exactly \(m\ge2\) blocks, all of the same rooted type, bear one order-\(h\) branch each; all other blocks have no such branch. The \(m\) marked vertices induce a connected subgraph of the core.
- Block orders have a common divisor \(g>mh\) and every block order exceeds \((m+1)h\).
- The high tails through \(s_v-h-1\) certify the multiset of rooted block types. The ordinary, unmarked types of any one order are pairwise distinguishable by their normalized profiles through deficit \(h-1\).

For \(m=2\) the ordinary chromatic symmetric function determines the whole tree among all trees. For \(m>2\) the same holds under the explicit rank test in Section 3. The marked and ordinary block orders can all be equal. A corollary for \(m=2\), \(h=3\): take any core with two adjacent marked vertices, equal block size \(s\ge10\), arbitrary mixtures of leaves and two-vertex branches off the ordinary roots, and identical rooted blocks at the two marked roots, each also bearing one three-vertex branch of either fixed rooted shape. No rank test is required in this corollary. The short-tail certification in [the single-marker proof](StanleyLargestBranchMarker.md#3-concrete-cutoff-three-family) verifies its assumptions.

## 1. Read the marker count of every core-cut component

Let \(U\) be the unsigned cut polynomial determined by the chromatic symmetric function, and define heavy edges at cutoff \(h\). The multiset of block types and the number \(q\) are recovered from the high layer of \(U\), for both the original tree and any rival. Write \(F_v(t)\) for the normalized block profile.

For a core cut, give each of its components an intact mass \(n_i\), the sum of the orders of the blocks it meets. A component with \(j_i>0\) marks is requested at visible mass \(n_i-j_i h\). Give each unmarked component a deficit \(d_i<h\). To obtain this data from \(U\), inspect the corresponding high monomial and extract \(x_h^m\) from its coefficient. Equivalently scan monomials of \(U\) with precisely \(m\) components of size \(h\): for each high size \(a>h\), set \(n=g\lceil a/g\rceil\), \(d=n-a\); retain only terms with intact masses summing to the total, every deficit either \(<h\) or a positive multiple \(jh\le mh\), and the sum of the positive \(j\)'s equal to \(m\). All queried visible masses exceed \(h\), since \(s_v>(m+1)h\).

Why does this extract the specified data? By \(mh<g\), any component at a queried size has intact mass at least its requested \(n_i\); equality and coverage of all the core vertices follow from the total-mass sum, as in the single-marker proof. A slot of deficit \(jh\) can detach at most \(j\) size-\(h\) components, and all slots at smaller deficit detach none. Since the target exponent is \(m=\sum j\), all slots must attain capacity. These detachments spend the entire deficit of every marked slot; each order-\(h\) branch must be detached intact and each belongs to a distinct marked block. As there are only \(m\) such branches, no mark lies in another slot. Thus each marked component is recovered with its intact mass and exact marker count, with coefficient 1 for the internal graft choices. An unmarked component \(C\) still contributes its low profile jet, written as the factor
\[
L_C=\sum_{d<h}[t^d]\left(\prod_{v\in C}F_v(t)\right)y_{n(C),d},
\]
with independent variables \(y_{n,d}\). This is commutative component data: identical slots need not be labeled. The monomial rule assigns the same output under any permutation of equal components and carries the original coefficient.

This readout certifies the connectivity hypothesis of the theorem. Among terms with one component containing all \(m\) marks, maximize the number of high components. To put the marks together, all edges in their minimal connecting subtree \(J\) must stay; one may cut every other core edge and use deficit zero on the unmarked slots. Hence the maximum is \(q-|E(J)|\), equal to \(q-m+1\) precisely when the marked vertices induce a connected subtree. This forces the same connectivity in any rival.

## 2. Recover the rooted bushes

In the marker-count data restrict to cuts with \(m\) singleton-mark components. All edges of the induced marked subtree are cut, since the marks are connected. Deleting those edges partitions the core into \(m\) rooted bushes \(B_i\), each rooted at its marked vertex. In our data give the singleton-mark component of intact mass \(a\) the variable \(z_a\). The resulting polynomial is
\[
P(z,y)=\prod_{i=1}^m f_i(z,y),\qquad
f_i(z,y)=\sum_{\text{core cuts of }B_i}
z_{\text{root mass}}\prod_{\substack{C\text{ component}\\C\text{ not at root}}}L_C.
\]

Over the field \(K(y)\), where \(K=\mathbb Q(x_1,\ldots,x_{h-1})\), each \(f_i\) is a nonzero linear form in \(z\), monic in the largest-index \(z\) that occurs. The coefficient of this largest index is exactly 1, from retaining every core edge of the bush. Unique factorization over \(K(y)\) thus gives the exact multiset of normalized forms, including repetitions. Their coefficients are in fact polynomials in \(y\). Substitute all \(z_a=1\) in a recovered \(f_i\): the single-marker decoding by branch factors now recovers the entire rooted, decorated bush. Use the same certified marked block type at each bush root; the individual unmarked rooted profiles are recovered by unit division, as before.

For \(m=2\) simply join the two bushes at their roots. Their order in the multiset and whether their forms coincide do not matter.

## 3. A rank test for more marks

For \(m>2\), suppose the recovered linear forms \(f_i\) are pairwise nonproportional over \(K(y)\), and for any distinct \(i,j,k\), \(f_k\) is not in the span of \(f_i,f_j\). These conditions are testable from the invariant. For example, distinct total bush masses give distinct leading \(z\) indices and make the entire collection linearly independent.

Take the terms with one two-mark component and \(m-2\) singleton-mark components. Each such term comes from retaining exactly one edge of the induced marked subtree, since all marked vertices belong to that subtree. Keep the \(z\) variables for the singleton marks but give the two-mark component factor 1 at every intact mass. If the retained edge joins bushes \(i,j\), the root components fuse; once the fused mass is summed out, the two bush cut choices are independent. The recovered polynomial is therefore
\[
Q(z,y)=\sum_{ij\in E(J)} f_i(\mathbf 1,y)f_j(\mathbf 1,y)
\prod_{k\notin\{i,j\}} f_k(z,y).
\]
Both displayed scalar factors are nonzero, having nonnegative coefficients and a nonzero intact-bush term. Reduce modulo \((f_i,f_j)\) in \(K(y)[z]\). All terms disappear except the potential \(ij\) term. The quotient is a polynomial ring over a field since the forms are independent; the other factors remain nonzero by the rank test. Thus the reduction detects exactly whether \(ij\) is an edge, recovering the tree of bushes.

[Exact checker](verify-stanley-connected-branch-markers.js) tests the extraction and connectivity certificate on an adjacent and a separated pair at cutoff two, matching all 10 symbolic coefficients over 2,097,152 full-tree edge subsets.

The branch-factor step and the final two-form test build directly on the [rooted \(U\)-polynomial theorem](https://doi.org/10.1016/j.disc.2020.112255) and the [prior connected-residue construction](StanleyTreeRootExtraction.md#2-several-indistinguishable-residues). Here the count comes from intact pendant detachments rather than a residue on the vertex weights; all marker and ordinary block orders may agree, unmarked grafts need not agree, and the bush profiles retain short-jet information about them. This is a restricted result, not the general Stanley conjecture.
