# Lieb permanental dominance for the natural action of A₇

**Catalogue #071.** For every complex Hermitian positive semidefinite \(7\times7\) matrix \(A=(a_{ij})\) and every nonzero finite-dimensional character \(\chi\) of the natural alternating subgroup \(A_7\le S_7\),
\[
 \frac1{\chi(e)}\sum_{\sigma\in A_7}\chi(\sigma)
                  \prod_{i=1}^7 a_{i,\sigma(i)}
 \le \operatorname{per}A .
\]
For each of the two degree-ten split irreducibles at a correlation matrix, the difference is at least \(\sum_{i<j}|a_{ij}|^2/20\). Thus for either split irreducible a positive-diagonal matrix attains equality exactly when it is diagonal. This is the complete natural **alternating subgroup** case, not a theorem for every subgroup of \(S_7\).

This continues the [order-six alternating case](FactorLiebAlternatingSix.md), but adds an ingredient needed for the imaginary split seven-cycle coefficient: mixed symmetric/exterior Gram matrices of partial cross-matchings, tested against complex Gaussian-integer vectors. The finite part is an explicit positive rational decomposition. Neither floating-point arithmetic nor a numerical optimizer is a premise.

## 1. Character reduction

An \(A_{ii}=0\) forces its whole row and column to vanish, so every monomial then vanishes. Otherwise normalize the positive diagonal to one by a diagonal congruence; all monomials scale back by the same factor \(\prod_i a_{ii}\). Restricting to irreducible characters suffices by the degree-weighted convex combination for direct sums.

The nonsplit restrictions are handled by the known ordinary order-seven immanant inequalities. In fact the normalized generalized matrix function of the restriction of \(\chi_\lambda\) from \(S_7\), when irreducible, is the average of the two normalized immanants for \(\lambda,\lambda'\), since the sign twist sends \(\lambda\) to \(\lambda'\). [Heyfron's result](https://doi.org/10.1017/S030500410006953X) covers order seven. The unique self-conjugate partition of seven is \((4,1^3)\), since the distinct odd diagonal hook lengths of a self-conjugate partition must sum to seven; only the single length seven is possible. Its \(S_7\) character is the exterior cube \(\eta\) of the standard representation, of degree \(\binom63=20\), and its restriction splits into two degree-ten characters.

Only the even cycle type \((7)\) splits as an \(A_7\)-class: the centralizer contains no odd permutation exactly for distinct odd cycle lengths. Choose the sign of a seven-cycle to be the parity of the list of its cyclically ordered entries; cyclic shifts are even, so the sign is well-defined. The two classes \(7^+,7^-\) have 360 elements each. Inversion interchanges them, since reversal of six entries has odd parity. So does conjugation by any odd permutation. On nonsplit even classes the two split characters are equal to \(\eta/2\). On 7-cycles their sum is \(\eta=-1\); their difference is purely imaginary, has opposite signs on the two classes, and has squared character norm two by irreducible orthogonality. Its modulus on a 7-cycle is therefore \(\sqrt7\). Thus the two values at \(7^+\) are \((-1\pm i\sqrt7)/2\), with opposite choices on \(7^-\); see also the [ATLAS degree-ten representations](https://brauer.maths.qmul.ac.uk/Atlas/v3/alt/A7/).

For \(m_\sigma=\prod_i a_{i,\sigma(i)}\), let \(U_\nu\) denote the real class sum over ordinary cycle type \(\nu\); write \(U_{7^+},U_{7^-}\) separately. The quantity
\[
   J=i(U_{7^+}-U_{7^-})
\]
is real because \(U_{7^-}=\overline{U_{7^+}}\). The two normalized split functions are the two choices \(f_{\pm\sqrt7}\) in
\[
 f_t= \sum_{\sigma\ \mathrm{even}}\frac{\eta(\sigma)}{20}m_\sigma+\frac{t}{20}J .
\tag{1}
\]
For computational purposes \(\eta(\sigma)\) is the coefficient of \(z^3\) in \(\prod_\ell(1-(-z)^\ell)/(1+z)\), with one factor per cycle of length \(\ell\). This is the characteristic determinant generating exterior powers after removing the constant subrepresentation. The certificate below establishes the inequality at \(t=8/3\) with the stated deficit; odd relabeling gives \(t=-8/3\), and \((8/3)^2>7\) makes (1) at both desired values a convex combination.

## 2. Positive generators: cross-matching Gram

For a fixed cut \(\{0,\ldots,a-1\}=X\), \(Y=\{a,\ldots,6\}\), and \(1\le k\le\min(|X|,|Y|)\), index by partial bijections \(\alpha:S_\alpha\to T_\alpha\) of size \(k\) from \(X\) to \(Y\). Set \(z_\alpha=\prod_{i\in S_\alpha}a_{i,\alpha(i)}\). Given flags \(d_X,d_Y\in\{0,1\}\), use a permanent for a mixed minor when its flag is zero, or a determinant when it is one. For \(Z=X,Y\) and deleted subsets \(S,S'\) of size \(k\), let \(G_Z[S,S']\) be the chosen minor on row list \(Z\setminus S\) and column list \(Z\setminus S'\), both sorted.

Each \(G_Z\) is a Gram matrix. If \(A_{ij}=\langle u_i,u_j\rangle\), linear in the second variable, these are the inner products of the symmetrized products \((m!)^{-1/2}\sum_\pi u_{\pi(1)}\otimes\cdots\otimes u_{\pi(m)}\) of the remaining vectors, or of the corresponding exterior products, with \(m=|Z|-k\). The empty product gives the scalar one. The matrix
\[
 K_{\alpha,\beta}
 =z_\alpha\overline{z_\beta}
     G_X[S_\alpha,S_\beta]\,
     \overline{G_Y[T_\alpha,T_\beta]}
\tag{2}
\]
is consequently positive semidefinite by pullback, entrywise product and diagonal congruence. In particular \(v^*Kv\ge0\) for **any** fixed vector \(v\) indexed by the partial bijections. No assumption that a separately phase-modified copy of \(A\) remains positive semidefinite is needed. We average these forms over all even relabelings of \(A\); their coefficient on each monomial is constant on the appropriate \(A_7\)-orbit. The ordinary unsigned first or higher cross-coefficient used below is the choice \(d_X=d_Y=0\) and \(v_\alpha=1\), equal to the sum of monomials of permutations with \(k\) arrows each way across the cut.

For clarity, the permutation expansion in (2) starts with the arrows \(\alpha\) and the reverse arrows \(\beta^{-1}\). It completes by independent assignments across the residual row and column lists inside \(X\) and inside \(Y\). A determinant flag gives the sign of that residual bijection. This explains how changing \(\bar v_\alpha v_\beta\) can alter the sign and phase of coefficients of whole cycles, while the entire expression stays nonnegative.

## 3. Positive generators: matching bounds

Let \(u_e=|a_{ij}|^2\) on an edge \(e=\{i,j\}\) and let \(D,M\) denote the sums of the products of \(u_e\) over matchings of sizes two and three in \(K_7\). Put \(S=\sum_e u_e\). Besides \(\operatorname{per}A-1\ge0\) (Lieb's block inequality), we use the three scalar generators
\[
 \begin{split}
  &4D-U_{3\,2},\\
  &2M-U_{3\,2^2},\\
  &(240/7)M+3U_7-4J .
 \end{split}
\tag{3}
\]
To check the first two, for a triple \(I\) the sum of its two oriented triangle monomials is at most \((2/3)\sum_{e\subset I}u_e\), by AM–GM and \(|a_{ij}|\le1\). Upon summing over disjoint swaps, a size-two matching occurs six times in the product bound for \(3\,2\) (choice of which edge is in the triangle, then one of three extra vertices). A size-three matching occurs three times for \(3\,2^2\) (choice of which edge is in the triangle, with the unique unused vertex completing it). This proves the first two bounds.

For an oriented seven-cycle remove one edge and take the two alternating three-matchings on the resulting six-edge path. Its absolute monomial is at most the average of the two products of \(u_e\) on these matchings, using Cauchy or AM–GM and the omitted edge modulus at most one. Averaging over all seven omissions weights each of its seven size-three matchings by \(1/7\), since a matching occurs for the two removals incident to its unmatched vertex. Every size-three matching of \(K_7\) appears in 48 oriented seven-cycles by permutation symmetry and \(720\cdot7/105=48\). Thus \(\sum_{\sigma:\mathrm{type}(\sigma)=7}|m_\sigma|\le(48/7)M\). If \(w=U_{7^+}\), then \(U_7=2\operatorname{Re}w\) and \(J=-2\operatorname{Im}w\), hence \(|3U_7-4J|\le10|w|\le 5\sum_{\mathrm{type}(\sigma)=7}|m_\sigma|\). This proves the last generator.

## 4. Explicit rational certificate

The fifteen generators are listed by their explicit flags, vectors and weights in [lieb_alternating_seven_certificate.json](lieb_alternating_seven_certificate.json). The seven scalar generators in that file are \(\operatorname{per}A-1\), the unsigned cross-coefficients at \((a,k)=(1,1),(2,1),(3,2)\), and the three entries of (3), in that order. The other eight are the averaged Gram forms (2), with labels starting at zero; a vector is a list of real/imaginary integer pairs. Its partial bijections are ordered lexicographically by increasing domain subset, then by ordered distinct image tuple. Each entry uses an explicit fixed vector, not an optimization.

With the weights \(w_l>0\) given there, the exact identity is
\[
 \operatorname{per}A-f_{8/3}-S/20
   =\sum_{l=1}^{15}w_l\,G_l(A),
\tag{4}
\]
where \(G_l\) are exactly those generators. This is a group-monomial coefficient identity. One can compute each column of its finite table as follows. For an ordinary cycle type, sum the real coefficients of its individual monomials before averaging and divide by its size. For seven-cycles, the real coefficient is computed the same way over all 720; the coefficient of \(J\) is \(\frac1{720}\sum_{\sigma:\mathrm{type}=7}\mathrm{signClass}(\sigma)\operatorname{Im}(\text{coefficient on }m_\sigma)\). On other classes conjugation-orbit inverse symmetry cancels all imaginary coefficients. This averaging is exactly the average over \(A_7\); all ordinary \(S_7\)-classes but the 7-cycles remain single \(A_7\)-conjugation orbits, including odd permutations whose centralizer contains an odd element. Alternatively, a literal coefficient can be recovered by extracting its two cross-matchings and its internal determinant signs. The companion program uses that latter method and verifies every stored column, all 5,040 target coefficients, the split coefficient \(-2/15\), the 360/360 conjugacy classes and the matching incidences \(6,3,48\). In particular it does not trust the expected columns in the certificate as inputs to the proof of the identity.

Run from the files' directory in ordinary Python, not with assertions disabled:

~~~sh
python3 verify_factor_lieb_alternating_seven.py
~~~

Only integer, Gaussian-integer and rational arithmetic is used. Nonnegativity of every generator is the analytic content of §§2–3. From (4) and the two-endpoint interpolation the split deficit is at least \(S/20\) on correlations; in the positive-diagonal matrix before scaling it is at least \((\prod_i a_{ii})\sum_{i<j}|a_{ij}|^2/(20a_{ii}a_{jj})\). This proves the theorem.

The alternating cases here should not be confused with the ordinary immanants of the full symmetric group, or with the projective-line degree-eight action of \(\mathrm{PSL}_2(7)\) in [Yi Yu's projective-action results](https://aixiv.online/abs/2611.03137). [Lieb's original paper](https://doi.org/10.1512/iumj.1967.16.16008) is the source of the general conjecture and block inequality. No result for arbitrary subgroups in degree seven, for the full all-order Lieb conjecture, or for permanent-on-top is claimed.
