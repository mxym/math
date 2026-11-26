# Odd prime-power coordinate elimination for spectral pairs

**Yongxian Zhang.** AI-assisted proof development and internal verification; no claim to fully settle Fuglede's conjecture.

**Theorem.** Let \(p\) be an odd prime, \(a\ge1\), and \(H\) a finite abelian group of exponent coprime to \(p\). Suppose \((A,\Lambda)\) is an \(m\)-point spectral pair in \(H\times\mathbb Z_{p^a}\), with \(p\nmid m\), under the product pairing. The projections of \(A\) onto \(H\) and of \(\Lambda\) onto \(\widehat H\) are injective and form an \(m\)-point spectral pair. Consequently \(A\) tiles \(H\times\mathbb Z_{p^a}\) if and only if its projection tiles \(H\).

This extends the exponent-one elimination theorem of [Tan–Zhang, arXiv:2610.02218v1, Theorem 2.3 and Corollary 2.4](https://arxiv.org/html/2610.02218v1#S2). It does not assume or require their square-free classification. We use and explicitly reproduce their off-block \(p\)-adic recurrence; the new step is to obtain its hypotheses separately on each frequency fiber at every prime-power depth. Neither \(p=2\) nor \(p\mid m\) is asserted.

## Recursive matrix lemma

Let \(R=\mathbb Z[\zeta_e]\) with \(p\nmid e\), and let a finite set of row labels carry coordinates \(i\in\mathbb Z_{p^a}\) (they need not be distinct). For \(j\in\mathbb Z_{p^a}\) let \(Q_j\) be Hermitian matrices over \(R\) with \(Q_j^2=mQ_j\). Set \(U_j=\operatorname{diag}(\zeta_{p^a}^{ij})\) on the rows. Suppose
\[
\sum_j U_j Q_jU_j^*=mI,\qquad m\in\mathbb Z_{>0},\quad p\nmid m.
\tag{1}
\]
We prove \(\sum_j Q_j=mI\) by induction on \(a\), the case \(a=0\) being immediate. Each \(U_jQ_jU_j^*/m\) is an orthogonal projection. Because their sum is the identity they are pairwise orthogonal: for a vector in the range of any one, its inner product with the sum of the others vanishes, and each summand is a squared projection norm.

Split the rows into residue blocks \(i\bmod p\). If rows \(i,i'\) are in different blocks, equation (1) gives
\[
\sum_{j=0}^{p^a-1}(Q_j)_{i,i'}\zeta_{p^a}^{(i-i')j}=0
\]
where repeated coordinates use the original row indices. The root in this equation is primitive. The field degree \([\mathbb Q(\zeta_e,\zeta_{p^a}):\mathbb Q(\zeta_e)]=\varphi(p^a)\) by coprimality; thus the minimal polynomial over \(\mathbb Q(\zeta_e)\) is \(\Phi_{p^a}(X)=\sum_{k=0}^{p-1}X^{kp^{a-1}}\). Polynomial division, with the quotient of degree below \(p^{a-1}\), shows that all coefficients at \(j=b+kp^{a-1}\), \(0\le b<p^{a-1}\), agree for fixed \(b\). Therefore for each \(b\) one has \(Q_{b+kp^{a-1}}=D_k+B_b\), with \(D_k\) block diagonal and \(B_b\) independent of \(k\), zero on diagonal blocks.

Write \(V_k=\operatorname{diag}(\zeta_p^{ik})\), so \(U_{b+kp^{a-1}}=U_b V_k\). Define \(D=\sum_k D_k\) for this fixed \(b\). Summing the twisted matrices over \(k\) gives \(U_b D U_b^*\): the diagonal blocks are unchanged by \(V_k\), and all other blocks cancel by \(\sum_k\zeta_p^{(i-i')k}=0\). Each twisted summand is an \(m\)-scaled orthogonal subprojection of that sum. Conjugating first by \(U_b^*\) and then by \(V_k^*\), which commutes with every block-diagonal matrix, gives
\[
D Q_{b+kp^{a-1}}=Q_{b+kp^{a-1}}D=mQ_{b+kp^{a-1}} .
\]
Taking off-diagonal blocks gives \(DB_b=B_bD=mB_b\). Now sum \(Q_{b+kp^{a-1}}^2=m Q_{b+kp^{a-1}}\) over \(k\); its off-diagonal blocks give
\[
p(B_b^2)_{\rm off}=m(p-2)B_b.
\]
Here \(m(p-2)\) is coprime to \(p\). If the entries of \(B_b\) lie in \(p^tR\), the left side has entries in \(p^{2t+1}R\), and an integer Bézout identity for \(m(p-2)\) and \(p^{t+1}\) forces the entries of \(B_b\) into \(p^{t+1}R\). Induction from \(t=0\), and the finite free \(\mathbb Z\)-module \(R\), imply \(B_b=0\).

All the \(Q_j\) are now block diagonal. Fix one residue \(i_0\), write each coordinate there as \(i_0+pi'\), and restrict the matrices to that block. The restrictions are still \(m\)-scaled orthogonal projections; all the twisted restrictions are pairwise orthogonal as well. For \(j=b+kp^{a-1}\) the restriction of \(U_j\) equals a scalar times \(\operatorname{diag}(\zeta_{p^{a-1}}^{i'b})\) on this block: the \(i_0\) factor is a scalar, and the \(i'\) factor depends only on \(b\). Thus the restricted \(Q_j\) with the same \(b\), after conjugation by a common diagonal unitary, are pairwise orthogonal. Their sum \(Q'_b\) is again \(m\)-idempotent over \(R\). Equation (1) on this block is the induction hypothesis with coordinates \(i'\), phases of order \(p^{a-1}\), and matrices \(Q'_b\). Hence \(\sum_b Q'_b=mI\) on the block. Summing the original \(Q_j\) blockwise proves the lemma.

## Applying the lemma

Rows of the square character matrix are indexed by \((x,i)\in A\), and columns by \((\lambda,j)\in\Lambda\); the entry is \(\lambda(x)\zeta_{p^a}^{ij}\). Let \(W_j\) consist of the columns at \(j\) after erasing the \(p^a\) phase. As the same unitary row scaling was erased from each column in that group, \(W_j^*W_j=mI\). The matrices \(Q_j=W_jW_j^*\) satisfy the lemma over \(R=\mathbb Z[\zeta_{\exp H}]\) by row orthogonality of the original matrix. Thus \(W W^*=mI\) for the full matrix with all those phases erased. In particular \(W\) is invertible. A projection collision of two spatial points or of two frequency points would make equal rows or columns, respectively. Both projections are therefore injective, and \(W\) verifies projected spectrality without any loss of cardinality.

## Consequences

* If the projected set \(B\subseteq H\) tiles with complement \(T\), then \(A\) tiles with \(T\times\mathbb Z_{p^a}\), since \(A\) is the graph of a function \(B\to\mathbb Z_{p^a}\). Conversely if \(A\) tiles, its projection tiles by dilation: for a tiling \(C+D=G\) with unique representations, and prime \(p\nmid |C|\), the group-ring Frobenius identity \(C^pD=|C|^{p-1}\sum_{g\in G}g\bmod p\) shows that \(pC+D\) is still a tiling with unique representations. Indeed the new nonnegative multiplicities are all \(1\bmod p\), sum to \(|G|\), and so all equal one. Repeat \(a\) times to embed \(p^aB\) into \(H\times\{0\}\); restricting the other tile to any fixed \(p^a\)-coordinate slice gives a complement in \(H\). The endomorphism of \(H\) given by multiplication by \(p^a\) is invertible. Also, in the other direction independently of tiling, if \(B\) is spectral in \(H\), its graph \(A\) is spectral with dual set \(\Lambda_B\times\{0\}\). Thus the reduction is an equivalence for both properties in the coprime-cardinality regime.
* Iteration in any odd cyclic group \(\mathbb Z_N\) reduces an \(m\)-point spectral set to the cyclic direct factor of order \(\prod_{p\mid m}p^{v_p(N)}\), with both sets injective under projection. In particular a spectral set of prime-power size \(q^b\) in an odd cyclic group tiles: after removing all other factors, use the prime-power cyclic Fuglede theorem. This holds even if \(q\nmid N\) formally, in which case the projection shows no such spectral set of size \(>1\) exists.
* For example, in odd order \(p^2q^2r\), any spectral set of size not divisible by at least one of \(p,q,r\) tiles. Eliminate that coordinate and apply the known two-prime cyclic cases: [Malikiosis, Forum of Mathematics, Sigma 10:e23 (2022)](https://doi.org/10.1017/fms.2022.14) and [Malikiosis–Kolountzakis, Discrete Analysis (2017)](https://arxiv.org/abs/1612.01328). The remaining regime has size divisible by all three primes. The independently established full result for large \(r\), [Fallon–Kiss–Mayeli–Somlai, arXiv:2308.16277v4](https://arxiv.org/abs/2308.16277), is not claimed here.
* Similarly, for odd order \(p^a q^b r s\), if \(p\nmid m\) or \(q\nmid m\), then the set tiles by reduction to the pertinent \(\mathbb Z_{q^b r s}\) or \(\mathbb Z_{p^a r s}\) theorem of [T. Zhang, Combinatorica 44 (2024)](https://arxiv.org/abs/2210.15174v2). Other regimes can be reduced if their eligible remaining factors fall within known families. No assertion is made about cases where every prime divisor of \(N\) divides \(m\).

The closest prior elimination argument located is Tan–Zhang's exponent-one theorem; their result already allows arbitrary coprime base groups \(H\), so novelty here is the depth of the deleted factor, not of the retained one. The argument is exact and uses no numerical spectral decisions.


**Why the matrix lemma does not cover \(p=2\).** Even with odd \(m\ge3\) and constant diagonal within each matrix, take \(Q_0=\mathbf 1\mathbf 1^*\), a diagonal \(V\) with both signs \(+1,-1\), and \(Q_1=mI-VQ_0V^*\). Both \(Q_j\) are \(m\)-idempotent and \(Q_0+VQ_1V^*=mI\), yet \(Q_0+Q_1\ne mI\). This is a counterexample only to the abstract matrix lemma at \(p=2\), not to spectral elimination for actual character matrices.
