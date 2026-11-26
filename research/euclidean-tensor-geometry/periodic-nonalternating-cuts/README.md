# Exact quantum max-flow for every nonalternating periodic cycle cut

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Let \(F\) be **any field**, and take a simple periodic cycle \(C_n\), \(n\ge3\), with a \(q\)-dimensional physical leg and \(q\)-dimensional bonds at each site, using the same tensor at every site. Fix a cut \(S\mid T\) of its physical legs and let \(\nu\) be the matching number of the cycle edges crossing that cut. For every **nonalternating** cut, the maximum flattening rank and the min-cut product both equal
\[
 q^\nu .
\]
The same integral local matrices work for all lengths, all nonalternating cuts and all fields at a fixed \(q\). Thus this includes every cut of an odd cycle and every cut with unequal side sizes. It is not a statement of general quantum max-flow/min-cut. The single-shared-tensor model and cut convention are those of [Gesmundo–Landsberg–Walter](https://arxiv.org/html/1801.09106#S1.SS4).

## The cut product

Give unit capacity to each edge of the extended cycle, which has one terminal leaf per cycle vertex. Integral max-flow/min-cut identifies the least edge-cut size with the maximum number of edge-disjoint paths from an \(S\)-terminal to a \(T\)-terminal. Two such paths cannot share a cycle vertex: they would need four different incident edges, and the extended cycle has degree three there. Each path has a crossing cycle edge. Choosing one from each path gives a matching, and every crossing matching supplies such paths by adjoining its terminal legs. The minimum number of cut edges is therefore \(\nu\), and the cut product is \(q^\nu\). Contracting after cutting also gives the usual rank upper bound over \(F\), by summing over the cut-edge label tuples. This argument for the cut product applies even to the alternating cut.

## One integral witness: the colored matching tensor

Index the physical labels and bond basis by \(0,\ldots,q-1\). Use
\[
 A_0=E_{00},\qquad A_a=E_{0a}+E_{a0}\quad(1\le a<q).
\]
In a closed walk contributing to \(\operatorname{tr}(A_{x_1}\cdots A_{x_n})\), every nonzero excursion goes from \(0\) to a leaf \(a\) and immediately back to \(0\) on the next site with the same label. A label \(0\) is a hub monomer. Thus a trace contribution is exactly a domino matching of the cycle with each chosen edge given a nonzero color \(a\), endpoint physical labels equal to that color, and all unused sites labeled zero. Closed walks are counted with the fixed location of site 1, including both matchings when a completely covered even cycle has two; this identity is valid even if they cancel in the field.

For each vertex \(v\), view its local space as the commutative algebra with basis \(1,x_{v,1},\ldots,x_{v,q-1}\), in which every product \(x_{v,a}x_{v,b}\) is zero. The trace tensor above is the product, in the tensor product of these algebras, of
\[
 1+\sum_{a=1}^{q-1}x_{u,a}x_{v,a}
\]
over the cycle edges \(uv\). Expansion retains exactly the disjoint colored edges. For an edge within \(S\) or within \(T\), multiplication by its factor is an invertible linear operator on that side: the nonconstant part squares to zero, so its inverse is obtained by subtracting it from 1. The flattening rank therefore equals that of the product over crossing edges alone.

The following forest fact proves attainment and is also valid for this colored matching tensor on any bipartite graph with an induced unique-perfect-matching maximizer. Fix a maximum matching of size \(\nu\), and select the flattening submatrix with every unmatched vertex assigned label zero. Its coefficients involve only the crossing graph induced on the matched endpoints. In a crossing forest the chosen matching is its unique perfect matching: two perfect matchings would give an alternating cycle. Identify the matched row and column endpoints with common indices \(1,\ldots,\nu\). Orient each extra crossing edge from its row index to its column index under that identification. A directed cycle would give an alternate perfect matching, so the extra edges form a directed acyclic graph. Choose a topological order, so each extra edge goes from a smaller index to a larger one.

In a nonzero expansion term for this submatrix, each nonzero row color at index \(i\) contributes one edge to a column of the same color, at index at least \(i\). Therefore the sum of indices carrying nonzero column labels is at least the analogous row sum, with strict inequality if any extra edge is used. Order rows and columns by this sum, breaking ties with the same word order. At equal sums only matched edges can occur. They give each equal row/column word coefficient one and each distinct equal-sum word coefficient zero. This proves the submatrix is triangular with unit diagonal and size \(q^\nu\), over every field. The crossing graph of a proper subset of the edges of a simple cycle is a forest, as needed.

For completeness, on an arbitrary bipartite graph the colored matching tensor's rank is at most \(q^\nu\). Choose a minimum vertex cover of size \(\nu\) by Kőnig's theorem, and assign each edge to one covering endpoint. The product of all factors assigned to one vertex \(v\) is \(1+\sum_a x_{v,a}\sum_{u}x_{u,a}\), where \(u\) ranges over its assigned neighbors; terms with two edges at \(v\) vanish. This is a sum of \(q\) simple tensors across the bipartition. The product of these sums is a sum of at most \(q^\nu\) simple tensors, since multiplication acts separately on the two sides. Hence the same exact matching-number formula for the colored matching tensor holds whenever some maximum matching's endpoints induce a unique perfect matching, in particular for every forest.

## Alternate witnesses and scope

The complex graph-state construction gives a different proof. The rank-one slices \(A_a=e_a y_a^{\mathsf T}\) on \(\mathbb Z/q\), with \((y_a)_b=\omega^{ab}\) for a primitive \(q\)-th root, give the cyclic coefficient \(\omega^{\sum_j x_jx_{j+1}}\). Within-side phases are invertible diagonal factors. For crossing biadjacency \(B\), the remaining matrix is \(\omega^{u^{\mathsf T}Bv}\), of rank \(|\mathrm{im}(B\bmod q)|\) by character orthogonality. In a forest the support of a square minor has at most one perfect matching. A maximum matching gives a \(\nu\)-square minor of determinant \(\pm1\), while all larger minors vanish. The Smith form of \(B\) then has \(\nu\) ones, giving the same result even for composite \(q\). This is the graph-state cut-rank mechanism of [Hein–Eisert–Briegel](https://arxiv.org/html/quant-ph/0307130). The colored matching witness above needs neither roots of unity nor a characteristic assumption.

Another useful path version holds over every field with more than two elements: choose any invertible entrywise nonzero \(q\times q\) matrix \(K\) and rank-one slices with overlap \(K\). After removing within-side factors and fixing unmatched labels to zero, the crossing forest has a perfect matching. At a leaf, multiply in that coordinate by the inverse of its edge matrix (possibly transposed). This identifies its neighbor's coordinate with the new leaf index and makes the matrix block diagonal by that index; conditioned extra edge factors are invertible diagonals on the remaining variables. Remove the matched endpoints and iterate. An invertible entrywise nonzero \(K\) is obtained from the all-ones matrix by changing each diagonal entry except the first to a field element other than zero and one. This also avoids roots-of-unity assumptions, but unlike the colored matching proof does not directly work over \(\mathbb F_2\).

Over \(\mathbb C\), combine this theorem with the separately known [four-cycle](https://github.com/mxym/math/releases/tag/periodic-ti-quantum-max-flow-v1.0.0), [odd-half-length](https://github.com/mxym/math/releases/tag/periodic-alternating-odd-half-lengths-v1.0.0), and [eight-cycle](https://github.com/mxym/math/releases/tag/periodic-eight-cycle-quantum-max-flow-v1.0.0) alternating classifications. The unresolved equal-dimension complex cycle cuts are thereby confined to strictly alternating cuts on lengths divisible by four not already resolved.

## Replay

Run `node verify-nonalternating.js`. The script checks 2,040 matching/min-cut instances, 1,846 direct modular trace ranks for the integral witness (including \(q=3,5\) over \(\mathbb F_2\)), and 1,028 weighted-overlap checks. The matching and triangular arguments prove the theorem without relying on these tests.
