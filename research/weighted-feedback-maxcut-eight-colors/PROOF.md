# A positive-facet reduction for weighted BEKSZ, and the eight-color case

AI-assisted research draft, independently reviewed internally but not externally refereed. No general weighted conclusion or priority claim. All weights are nonnegative real numbers on unordered distinct vertex pairs. Let W be their sum, C their maximum cut, d_i the weighted degrees and K(d)=E|Σd_i ε_i| for independent uniform signs. The expression H(w)=2W/5+(4/15)K(d) is exactly the homogeneous right side of [BEKSZ, ITCS 2025, Conjecture 3](https://doi.org/10.4230/LIPIcs.ITCS.2025.22); it is Conjecture 1.3 in the [ECCC revision](https://eccc.weizmann.ac.il/report/2022/179/revision/1/download/). The conclusion proved here is H(w)≤C for arbitrary weights whenever the graph of strictly positive edges is eight-colorable.

## 1. Reduction valid at any order

**Contraction.** If w_ij=0, identify i and j, summing weights on parallel pairs. W stays fixed. Every cut of the contraction lifts, so C cannot increase. Degrees outside the pair are unchanged; replace d_i,d_j by d_i+d_j. Conditional on the other signs giving sum T, the old expectation over the two signs is
(1/2)max(|T|,d_i+d_j)+(1/2)max(|T|,|d_i−d_j|); the new one is max(|T|,d_i+d_j). Thus H cannot decrease. In particular a counterexample with a k-colorable positive edge support yields one on ≤k vertices by identifying vertices in each independent color class. No positive edge is turned into a loop. This argument cannot be used to merge adjacent vertices.

Suppose a counterexample exists, and minimize its vertex count n. C>0; normalize C=1 by homogeneity. On the edge coordinates of K_n consider the polytope B={w≥0: w·δ_S≤1 for every cut indicator δ_S}. Nonnegativity and the singleton cuts give 0≤w_e≤1. Thus B is compact. H is convex (expectation of absolute linear forms plus a linear functional) and homogeneous; some maximizing vertex u of B also violates H(u)≤1. If u had a zero coordinate, contraction would contradict minimal n, since H stays >1 and C stays ≤1. Therefore u>0 coordinatewise.

Since u is a vertex of B, the cut vectors with u·δ=1 span the whole edge space: otherwise there is a nonzero orthogonal perturbation, and positivity plus the finitely many strict cut inequalities gives a small feasible perturbation in both directions. Since all the active vectors lie on u·δ=1, their affine dimension is |E|−1. The cut polytope CUTP(K_n)=conv{δ_S} is full dimensional: the origin is a cut and, for each edge ij, twice its coordinate unit vector is δ_{i}+δ_{j}−δ_{i,j} (subscripts denote 1- or 2-element sets). Thus u·x≤1 is facet defining. Conversely, for any facet with strictly positive outward normal a and upper constant b, one has b=max_S a·δ_S>0. Its active cuts affinely span dimension |E|−1 in a hyperplane not through 0, hence linearly span the edge space; therefore a/b is a vertex of B. This identifies the strictly positive vertices of B exactly. No assertion is made that every facet class admits a strictly positive transform.

**Conclusion of reduction.** To exclude all counterexamples of order ≤k it is enough to prove H(a)≤C(a) for the full-support positive representatives of the cut-polytope facets at orders through k. It is not enough to consider only CUTP(K_k)'s strictly positive facets without smaller orders, because zero weights may contract to smaller graphs.

## 2. Orders 2–4 without any catalog

For nonnegative weights and W>0 all degrees lie in [0,W] and sum to 2W. The convex symmetric K on this box section attains its maximum at (W,W,0,…), up to permutation, since every vertex has at most one coordinate not at an endpoint and the total is 2W. Thus K≤W. For any graph on ≤4 vertices, pad to four vertices and take uniformly a two-versus-two bipartition. Every edge is cut with probability 2/3. Hence C≥2W/3≥H. The zero-weight and order≤1 cases are immediate.

## 3. Published facet enumeration at orders 5–8

The [Heidelberg SMAPO tables](https://comopt.ifi.uni-heidelberg.de/software/SMAPO/cut/cut.html) give respectively 2, 3, 11 and 147 facet classes at orders 5,6,7,8 **under vertex permutations and switching**. The order-8 status line of the original data site predates definitive completeness: see [Deza and Dutour Sikirić, §3](https://arxiv.org/pdf/1501.05407), which proves the Christof–Reinelt list complete. For the lower orders also see [Grishukhin (1990), K7](https://doi.org/10.1016/S0195-6698(13)80064-9) and the same data page. The source rows for this check are inequalities a·x≤0 in the edge order AB,AC,… (lexicographically ordered vertex pairs). The coefficient rows are read from the four original sources linked in SOURCES.md. The input parser checks their dimension, edge order, numbering, inequality direction and SHA-256 of the complete canonical coefficient list. The catalog itself is not redistributed here. Their mathematical completeness is an external input, not proved by our code.

Switching by a sign vector s changes the coefficient a_ij to a_ij s_i s_j: on a crossed edge the coordinate x_ij changes to 1−x_ij, shifting the right-hand constant as well. We **do not retain the zero right-hand constant after switching.** For a transformed positive vector w we compute its actual C(w) by direct enumeration. Check one sign vector per complementary pair by fixing s_1=+1. Permuting the vertices just permutes weights/degrees, signs and cuts, so further label permutations are unnecessary. Zero entries are unchanged by switching. There is at most one successful switching per full-support representative with s_1=+1 (the signs relative to vertex 1 are forced).

For each full positive transform w, compute W=Σw_ij, d_i=Σ_j w_ij, C=max over the 2^(n−1) cuts, and K=2^(1−n)Σ_{s:s_1=+1}|Σ d_i s_i|, all exactly as integers/rationals. The following is the minimum of (15C−6W−4K)/C among the successful rows; a zero means equality for that positive facet, not classification of equality for general weights.

| n | source orbits | admit strict positivity | min relative gap | zero source row |
|---|---:|---:|---:|---|
| 5 | 2 | 1 | 0 | 1 (uniform clique) |
| 6 | 3 | 1 | 5/12 | none |
| 7 | 11 | 4 | 1/8 | none |
| 8 | 147 | 29 | 11/32 | none |

The fail-closed script verify.py reproduces the table and checks each inequality, not just the minima. Since a least-order counterexample on ≤8 vertices would give one of these strictly positive facets, none exists. Contraction then establishes the stated all-orders eight-color theorem. The procedure does not prove anything unrestricted from a list of candidates in an incomplete facet catalog, and the weighted open conjecture and channel question are not resolved.
