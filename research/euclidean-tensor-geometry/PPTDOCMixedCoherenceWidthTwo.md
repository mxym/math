# A two-sparse separability certificate for mixed PPT DOC compositions

## Statement

Use the convention \(\Phi_{A,B,C}(E_{ii})=\sum_k A_{ki}E_{kk}\), and for \(i\ne j\), \(\Phi_{A,B,C}(E_{ij})=B_{ij}E_{ij}+C_{ji}E_{ji}\). The three matrices have common diagonal. A positive-partial-transpose (PPT) diagonal-orthogonal-covariant (DOC) map is equivalently specified by \(A\) entrywise nonnegative, \(B,C\) Hermitian positive semidefinite, and
\[
\max(|B_{ij}|,|C_{ij}|)^2\le A_{ij}A_{ji}.
\]
For another PPT DOC triple \((D,E,F)\), define \(a_i=A_{ii}\), \(d_i=D_{ii}\), and zero-diagonal real symmetric matrices
\[
U_{ij}=\min(|B_{ij}|,|C_{ij}|),\qquad V_{ij}=\min(|E_{ij}|,|F_{ij}|)\quad(i\ne j).
\]
If \(\operatorname{diag}(a_i d_i)-U\circ V\succeq 0\), both orders of composition are entanglement breaking. More strongly, each of their Choi matrices is a sum of separable matrices supported on common two-index local subspaces. In particular both orders are entanglement breaking if \(\operatorname{diag}(a)-U\succeq0\), or if \(\operatorname{diag}(d)-V\succeq0\). This holds when *any one* of \(B,C,E,F\) has factor width at most two, and neither factor need be entanglement breaking or belong to a diagonal-unitary-covariant subclass. No trace-preservation hypothesis is needed.

## Proof

The rearrangement bound for two nonnegative numbers from each factor shows that both coherence entries of the composite, for either order, have modulus at most \(p_{ij}r_{ij}+q_{ij}s_{ij}\). Here \(p=\max(|B_{ij}|,|C_{ij}|)\), \(q=\min(|B_{ij}|,|C_{ij}|)\), and \(r,s\) are the corresponding maximum and minimum for \(E,F\). Indeed each of the two coefficients is the sum of two products with the two possible matchings. In the ordered basis \((E_{ij},E_{ji})\) the coherence block is
\[
\begin{pmatrix}B_{ij}&C_{ij}\\\overline{C_{ij}}&\overline{B_{ij}}\end{pmatrix},
\]
and similarly with \(E,F\) for the other factor. Ordinary block multiplication gives the matching property in either order.

For order \(AD\), let \(\alpha_{ij}=A_{ij}D_{ji}\), so \(g_{ij}=\sqrt{\alpha_{ij}\alpha_{ji}}\ge p_{ij}r_{ij}\) by PPT of both factors. Also \((AD)_{ii}=a_i d_i+\sum_{j\ne i}\alpha_{ij}\). For the reverse order replace \(\alpha_{ij}\) by \(\alpha_{ji}\); this does not change \(g_{ij}\).

Let \(m_{ij}\) be the maximum modulus of the two composite coherence entries. Its comparison matrix \(L\) has diagonal \((AD)_{ii}\) and off-diagonal \(-m_{ij}\). Put \(w_{ij}=\min(m_{ij},g_{ij})\). For every pair \(i<j\), subtract from \(L\) the supported block with diagonal \((\alpha_{ij},\alpha_{ji})\) and off-diagonal \(-w_{ij}\). Each subtracted block is positive semidefinite. The residual has diagonal \(a_i d_i\) and off-diagonal \(-(m_{ij}-g_{ij})_+\), where
\[
0\le(m_{ij}-g_{ij})_+\le q_{ij}s_{ij}.
\]
For symmetric nonnegative zero-diagonal \(T'\le T\), positivity of \(\operatorname{diag}(h)-T\) implies positivity of \(\operatorname{diag}(h)-T'\) by applying the former to the entrywise absolute value of an arbitrary test vector. Thus \(L\succeq0\) under the proposed condition. This also proves the sharper, order-specific sufficient test using the exact residual \((m-g)_+\) instead of \(U\circ V\).

For clarity, here is an elementary proof that positivity of \(L\) suffices. Because the composite is PPT (complete positivity and complete copositivity are preserved under composition of PPT maps), \((AD)_{ij}(AD)_{ji}\ge m_{ij}^2\). On the positive diagonal support of \(L\) normalize its diagonal to the identity. Each component of the nonnegative off-diagonal magnitude matrix has a strictly positive Perron vector; its Perron root is at most one by \(L\succeq0\). Undoing normalization provides \(x_i>0\) with \(\sum_{j\ne i} m_{ij}x_j\le (AD)_{ii}x_i\). Zero diagonal vertices have zero coherence and can be left out. For each \(i<j\) allocate classical entries \((AD)_{ij},(AD)_{ji}\) and diagonal budget \(m_{ij}x_j/x_i,m_{ij}x_i/x_j\) to the two-index Choi block, with its two original coherence coefficients. Both pairs of diagonal entries have products at least \(m_{ij}^2\). The block is PPT on a \(2\otimes2\) subsystem (use the two \(2\times2\) principal blocks and their partial transposes), hence separable by the Peres–Horodecki theorem. Leftover diagonal entries are themselves separable. Conversely, a sum of separable Choi terms each supported on at most two common local indices forces \(L\succeq0\): twirl the summands by diagonal signs; each two-index term has a nonnegative diagonal budget product at least the square of its own maximum coherence, so the corresponding comparison block is PSD. Group terms at each pair and use the triangle inequality and increasing-offdiagonal-magnitude monotonicity just proved. Thus \(L\succeq0\) is also necessary for this particular type of decomposition.

If \(\operatorname{diag}(a)-U\succeq0\), conjugate by \(\operatorname{diag}(\sqrt{d_i})\) and use \(V_{ij}\le\sqrt{d_i d_j}\). Then monotonicity gives the joint hypothesis; the other factor is symmetric. If one coherence matrix has factor width at most two, its comparison matrix is PSD: decompose it into positive rank-one matrices supported on at most two coordinates, take each comparison matrix, and use the triangle inequality and monotonicity on their sum. Since \(U\) is entrywise bounded by either coherence magnitude, this proves the advertised special case.

## Triangle-free coherence supports

Call a coherence graph the graph of its nonzero off-diagonal entries. If each map has at least one coherence graph that is triangle-free, the criterion is automatic (the two graph choices need not agree). In particular the square of a PPT DOC map is entanglement breaking if either coherence graph is triangle-free, with arbitrary complex phases on its edges.

To prove this, let \(M\) be a positive semidefinite matrix with diagonal \(a_i\) and triangle-free coherence support. Delete zero-diagonal rows and columns, and divide each entry by \(\sqrt{a_i a_j}\) to obtain the Gram matrix of unit vectors \(v_i\). For fixed \(i\), its neighbor vectors \(v_j\) are orthonormal, since triangle-freeness forbids edges between distinct neighbors. Bessel's inequality gives \(\sum_{j\ne i}|M_{ij}|^2/(a_i a_j)\le1\). Since \(U_{ij}\le|M_{ij}|\), the same inequality holds for \(U\); the analogous inequality holds for \(V\). Cauchy–Schwarz now gives every row sum of the nonnegative normalized matrix \(U_{ij}V_{ij}/\sqrt{a_i d_i a_j d_j}\) at most one. Symmetry and diagonal dominance prove the joint PSD hypothesis. This is genuinely beyond the single factor-width criterion: the phases on a cycle can make its coherence matrix have factor width greater than two even though its graph is triangle-free.

## A four-dimensional bistochastic example outside the two published sufficient tests

Take \(t=2/3\), \(A=I+t\,\mathrm{Adj}(C_4)\) on cyclic indices \(1,2,3,4\), \(B=I+t(E_{12}+E_{21})\), and \(C=I+tH\), where \(H\) is the real symmetric cyclic adjacency with three positive edges and the \(41\) edge negative. Scale all three matrices by \(1/(1+2t)=3/7\). We do calculations before this common scaling; all relevant inequalities are homogeneous. \(H^2=2I\), so \(C\) is positive definite, and \(B\) is positive definite with factor width two. The edgewise PPT inequalities hold. The common scaling yields a trace-preserving unital map by the column and row sums of \(A\).

The channel is not entanglement breaking. In any product-vector separable representation, both local supports intersect in a set \(S\) which must be a clique of \(C_4\): two distinct indices in \(S\) force the two associated cross diagonal entries to be positive, impossible at a nonedge. Thus \(|S|\le2\). After the diagonal-sign twirl, the \(C\)-coherence of each summand is a rank-one outer product of the coordinate products (conjugating one local vector) supported on \(S\), including its diagonal. It follows that \(C\) would have factor width at most two, impossible since its comparison matrix \(I-t\,\mathrm{Adj}(C_4)\) has eigenvalue \(1-2t<0\).

The square is EB by the new criterion. Nechita–Park Proposition 6.2 does not certify it: for the \(12\) edge one of the output coherences has modulus \(2t^2=8/9\), greater than the uniform per-edge budget \(t^2+1/3=7/9\). Their Corollary 6.4 does not apply since both off-diagonal coherence sectors are nonzero. The Marquez Gonzalez purely classical toroidal condition does not certify it: \((A^2)_{12}=2t=4/3\), below its universal coefficient \(4\). Its rank-sensitive refinement also uses coefficient \(4\): the two Schur-sum matrices prior to normalization in Eq. (39) have diagonal \(2\) before scaling and are strictly diagonally dominant (their largest off-diagonal absolute row sum is \(8/9+4/9=4/3\)). Hence both normalized correlations have rank four.

There is also a version beyond *all* one-coherence factor-width tests: retain \(A\) and take \(B=C=I+tH\). Neither input coherence matrix now has factor width two, and the input is still PPT and not EB by the same argument. Both composite coherences have modulus \(2t^2\) on every cyclic edge, so Nechita–Park's uniform inequality fails on every such edge. Both Schur-sum matrices for the toroidal test have diagonal \(2\) and absolute row sum off the diagonal \(4t^2=16/9<2\), so have full rank; the same toroidal inequalities fail. The triangle-free theorem nevertheless applies, as does the direct comparison test: the normalized matrix \(U\circ V\) has absolute row sum \(2t^2=8/9\).

## Context and sources

The comparison criterion for a common two-index decomposition packages the two PPT coherences with an entrywise maximum; separate comparison matrices are not sufficient. The edge diagonal contributions are the same ones used for a single sector in Singh–Nechita, and allocation of an equal share of the base diagonal to all edges gives Nechita–Park's earlier sufficient condition. The added estimate here is to spend only the matched maximum product from these contributions, leaving the minimum-product residual to a single comparison test. Singh's triangle-free result concerns *input-state entanglement detection* from the classical diagonal zero pattern, not separability of the composition from coherence supports.

- Satvik Singh and Ion Nechita, [The PPT² conjecture holds for all Choi-type maps](https://doi.org/10.1007/s00023-022-01166-0), Theorem 4.5, for (conjugate) diagonal unitary covariance; their factor-width criteria also underpin the argument.
- Satvik Singh, [Entanglement detection in triangle-free quantum states](https://doi.org/10.1103/PhysRevA.103.032436), comparison-matrix entanglement detection for the Choi input example.
- Aabhas Gulati, Ion Nechita and Satvik Singh, [Entanglement in cyclic sign invariant quantum states](https://arxiv.org/html/2501.04786v2), Section VII, selected cyclic-symmetry composition cases, not the arbitrary triangle-free support criterion.
- Ion Nechita and Sang-Jun Park, [Random covariant quantum channels](https://doi.org/10.1007/s00023-025-01558-y), Proposition 6.2, Corollary 6.4: uniform edge-budget sufficient condition and mixed DOC with a DUC/CDUC map; Theorem 6.5 is a random result.
- Samuel Marquez Gonzalez, [Toroidal-core certificates](https://arxiv.org/abs/2609.32979), arbitrary-dimension sufficient entrywise classical mixing test.
- OpenAI, [family 272](https://github.com/openai/math/blob/main/lean/docs/272.md), Theorems 1.2 and 1.3 of the associated preprint: a counterexample with distinct PPT maps on matrices of size ten (effective intermediate dimension six) and a trace-preserving same-channel counterexample in dimension 21.
- Tejasvi Singh Tomar, [On the minimal dimension of range-criterion counterexamples](https://hexagonmath.org/pdf/2611.00387v1), Theorem 1.1 and 4.20, excludes a product-free composite range certification in dimension four, not any conceivable entangled composition. Theorem 6.13 has separate SU(2)-covariant results. The numerical identifier is Hexagon, not arXiv.

A barrier to proving universal DOC behavior solely by two-index blocks already appears for \(d=4\): choose \(A=B=C=J_4\), the all-ones matrix, scaled by \(1/4\) for a channel. This input is separable by the single TCP atom of two all-ones vectors, hence its square is EB. Before scaling the square's common diagonal is \(4\) and both coherence magnitudes are \(2\) on every edge. Its maximum comparison matrix has all-ones eigenvalue \(4-3\cdot 2=-2\), ruling out every common two-index decomposition despite separability. Thus failure of the comparison test cannot by itself witness an entangled composite.

This note does not establish the full DOC dimension-four case or determine the minimum dimension of a general counterexample. The new estimate is a sufficient condition on two presented PPT maps in one common DOC basis, not a general PPT² assertion.
