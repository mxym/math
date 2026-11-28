# Lieb permanental dominance for the natural action of A₈

**Catalogue #071.** Let \(A=(a_{ij})\) be any complex Hermitian positive semidefinite \(8\times8\) matrix. For every nonzero finite-dimensional character \(\chi\) of the natural alternating subgroup \(A_8\le S_8\),
\[
 \frac1{\chi(e)}\sum_{\sigma\in A_8}\chi(\sigma)\prod_{i=1}^8 a_{i,\sigma(i)}
      \le \operatorname{per}A.
\]
On a correlation matrix, each of the four split irreducibles (two of degree 45, two of degree 21) has deficit at least \(\frac1{20}\sum_{i<j}|a_{ij}|^2\). For these four characters, the positive-diagonal equality case is exactly a diagonal matrix. This extends the [six-point](FactorLiebAlternatingSix.md) and [seven-point](FactorLiebAlternatingSeven.md) natural alternating actions. It is not an all-subgroups result in order eight, nor an all-order resolution.

Two different split-class differences are imaginary at this order. They are controlled by two exact positive rational certificates, each using the mixed symmetric/exterior cross-matching forms from the seven-point work. The checker rederives every coefficient by exact arithmetic.

## 1. Character coordinates

A zero diagonal entry in a positive semidefinite matrix forces the corresponding row and column to be zero, so all monomials vanish. Otherwise normalize the diagonal to one; all monomials scale back by the same positive factor \(\prod_i a_{ii}\). It suffices to consider irreducibles because normalized direct sums are degree-weighted convex combinations.

For an \(S_8\) partition \(\lambda\ne\lambda'\), the irreducible restriction to \(A_8\) has normalized function equal to the average of the normalized ordinary immanants for \(\lambda,\lambda'\), since their characters differ by a sign twist. Those immanants obey the inequality by [Pate, *Tensor inequalities, ξ-functions and inequalities involving immanants*, Theorem 3](https://doi.org/10.1016/S0024-3795(99)00035-X), whose range includes order eight.

There are exactly two self-conjugate partitions of eight, with the following diagonal hook types and symmetric-group dimensions:
\[
   \lambda_1=(4,2,1,1),\quad \nu_1=(7,1),\quad f_1=90;
   \qquad
   \lambda_2=(3,3,2),\quad \nu_2=(5,3),\quad f_2=42 .
\]
Their classification follows from the distinct odd diagonal hook lengths summing to eight, and their degrees follow from the hook-length formula. The two \(\nu_i\) are also the only two ordinary cycle types that split into two even-conjugacy classes. Order the cycles by decreasing length and concatenate their cyclic words; the parity \(\varepsilon(\sigma)\) of this list distinguishes the two classes. A change of cyclic starting point in an odd cycle does not change parity. For both types inversion changes parity, since the reversal parities have total exponent \(\sum_{\ell\in\nu_i}(\ell-1)/2=3\). Odd conjugation also changes parity.

Write \(m_\sigma=\prod_i a_{i,\sigma(i)}\), and \(U_\mu\) for the sum over all permutations of ordinary type \(\mu\), omitting trailing fixed points when convenient. Put \(J_\nu=i\sum_{\operatorname{type}(\sigma)=\nu}\varepsilon(\sigma)m_\sigma\) at a split type; it is real by Hermitian symmetry and inverse exchange. The standard split-character formula (for example [Fulton–Harris §5, Frobenius's formula](https://mat.uab.cat/~pitsch/ReadingSeminar/Fulton-Harris.pdf)) says the characters are half the parent character except for a difference supported on the diagonal hook type, where the two values differ by \(\sqrt{(-1)^3\prod_{\ell\in\nu}\ell}\). Hence the normalized split functions are the two choices \(f_{\lambda,\pm\sqrt{\prod_{\ell\in\nu}\ell}}\) in
\[
 f_{\lambda,t}
  =\sum_{\sigma\in A_8}\frac{\chi_\lambda(\sigma)}{f_\lambda}m_\sigma
     +\frac{t}{f_\lambda}J_\nu.
\tag{1}
\]
We certify \(t=8/3>\sqrt7\) for \(\lambda_1\) and \(t=4>\sqrt{15}\) for \(\lambda_2\). The opposite rational endpoints follow by odd relabeling, and interpolation gives both split branches. Cancellation of the unneeded imaginary coordinate is checked in each certificate.

## 2. Nonnegative Gram and principal generators

For an initial block \(V_0\) of \(v\le8\) vertices and a cut \(V_0=X\sqcup Y\) with \(X\) the first \(a\) vertices, index crossing partial bijections \(\alpha:S_\alpha\to T_\alpha\) of size \(k\) from \(X\) to \(Y\). Let \(z_\alpha=\prod_{i\in S_\alpha}a_{i,\alpha(i)}\). Form the matrix \(G_X[S_\alpha,S_\beta]\) of mixed minors of \(A[X]\) obtained by deleting rows \(S_\alpha\) and columns \(S_\beta\), either all permanent minors or all determinant minors; make the same independent choice in \(Y\). These are Gram matrices of the remaining symmetric or exterior products of the original Gram vectors (inner product linear in the second variable), with sorted lists and empty products allowed. The symmetric product of \(m\) vectors is \((m!)^{-1/2}\) times the sum over their ordered tensor permutations; the exterior product has the usual determinant inner product. Thus
\[
 K_{\alpha\beta}
     =z_\alpha\overline{z_\beta}\,
       G_X[S_\alpha,S_\beta]\,
       \overline{G_Y[T_\alpha,T_\beta]}
\]
is positive semidefinite by pullback, entrywise product and diagonal congruence. It follows that \(q^*Kq\ge0\) for any fixed vector \(q\), including the complex Gaussian-integer vectors in the certificate. The label **gram** uses the full eight-vertex set and the two flags \(0=\mathrm{per}\), \(1=\det\); index the partial bijections in lexicographic order of the increasing domain subset, then the ordered image tuple, on labels \(0,\ldots,7\). The label **cross** is the all-ones weight with both permanent flags on the specified principal size \(v\), hence includes exactly the permutations with \(k\) arrows in either direction across the cut. This is related to the positive tensor filters of [Pate's 1997 generalized-matrix-function framework](https://doi.org/10.1016/S0024-3795(96)00512-5); here it provides coefficients on alternating conjugacy orbits, including the two imaginary directions.

For a vertex set \(Z\), set \(P_Z=\operatorname{per}A[Z]\) and \(\Delta_Z=\det A[Z]\). \(P_Z\ge1\) by Lieb's block inequality and \(0\le\Delta_Z\le1\) by positivity and Hadamard. The labels **per-1** and **per-det** on an initial block mean \(P_Z-1\) and \(P_Z-\Delta_Z\). **Fischer** is \(\Delta_X\Delta_Y-\Delta_{X\cup Y}\ge0\) for the specified cut of the initial block. **prod** uses disjoint consecutive blocks of sizes \(a,b\) starting at zero and chooses two factors indexed by \(0,\ldots,4\) from
\[
                  P_Z,\quad\Delta_Z,\quad P_Z-1,\quad1-\Delta_Z,\quad P_Z-\Delta_Z.
\]
Every such factor is nonnegative. Each primitive involving selected labels is averaged over even relabelings. A permutation not supported in its principal block has zero coefficient in that primitive.

## 3. Nonnegative scalar generators

Let \(w_e=|a_{ij}|\), \(u_e=w_e^2\), \(S=\sum_e u_e\), and let \(D,M,N\) be the matching sums of sizes two, three, and four with edge weights \(u_e\) in \(K_8\). We have \(0\le u_e\le1\).

**Cubic spectrum.** The eigenvalues \(x_i\) of \(A-I\) satisfy \(x_i\ge-1\), \(\sum_i x_i=0\), \(\sum_i x_i^2=2S\), and \(\sum_i x_i^3=3U_3\). Summing \((x_i+1)(x_i-2S/8)^2\ge0\) gives \(U_3\ge-\frac23S+\frac16S^2\). Also \(D\le3S^2/8\): consider the graph in which edges of \(K_8\) are adjacent when disjoint. A fixed-mass maximizer of \(D\) with minimal support has no two nonadjacent positive weights, since one can merge their mass toward the larger linear neighbor sum. Its support is at most four, which gives the claimed bound by Cauchy. This proves \(U_3+\frac23S-\frac49D\ge0\) (the **triangle MS** row).

**Two triangles, with or without a swap.** For a triple \(T\), let \(S_T=\sum_{e\subset T}u_e\), and \(z_T\) be the sum of its two oriented triangle monomials. We have \(-S_T/3\le z_T\le2S_T/3\): the negative bound follows from AM–GM if \(S_T\le3/4\), and from \(1-S_T+z_T\ge0\) otherwise. The positive bound uses AM–GM and \(S_T\le3\). For disjoint triples \(T,W\), \(z_Tz_W\ge-(2/9)S_TS_W\). A pair of disjoint edges occurs twelve times in the sum of \(S_TS_W\) over unordered disjoint triples, by extending each of the two edges from two distinct choices among four unused vertices. Thus \(U_{3^2}+\frac83D\ge0\). For a swap on the remaining edge, each size-three matching is counted six times: choose its swap from three edges and assign the two unused vertices to the two triangles. Thus \(U_{3^2\,2}+\frac43M\ge0\).

**Four-cycles and \(4+4\).** The two alternate matchings of a four-cycle bound its absolute monomial by the average of their two products of \(u_e\). A fixed pair matching on a four-set occurs in four oriented cycles, so the absolute sum over the four-set is at most twice its pair matching sum. This gives \(2D\pm U_4\ge0\). With two cycles covering complementary four-sets, each full size-four matching occurs in three divisions into two edge pairs. Applying the four-set bound separately on both sides gives \(12N\pm U_{4^2}\ge0\).

**Five-cycles and \(5+3\).** For a five-cycle delete one edge and bound the product by the average products of \(u_e\) on the two alternating matchings of the resulting path, since the deleted modulus is at most one. Averaging the five deletions gives each disjoint pair in the cycle weight \(1/5\). A fixed pair matching within a five-set occurs in eight oriented cycles. On eight vertices there are four choices of the extra vertex extending each pair matching to a five-set, so the absolute sum over type \(5\,1^3\) is at most \((32/5)D\). For \(5+3\), fix a triangle \(T\); its sum of absolute orientation monomials is at most \(2S_T/3\), while the five-side sum is at most \((8/5)D_{T^c}\). A size-three matching occurs six times in \(\sum_T S_T D_{T^c}\) by choosing its triangle edge and one of the two unused vertices. Hence the absolute sum over type \(5\,3\) is at most \((32/5)M\). Since inverse exchanges the two split classes, writing \(h=U_{53,+}\) gives \(U_{5\,3}=2\operatorname{Re}h\), \(J_{53}=-2\operatorname{Im}h\), and
\[
           |aU_{5\,3}+bJ_{53}|\le\sqrt{a^2+b^2}\,\frac{32}{5}M.
\]
The two **joint** rows use \((a,b,c)=(4,3,5),(12,5,13)\) and their specified signs. Finally \(M\le2D\): each three-matching has three two-edge submatchings, and for a given two-edge matching the sum of weights of admissible third edges is at most six. This gives **cap**.

## 4. Two exact rational identities

The files [lieb_alternating_eight_certificates.json](lieb_alternating_eight_certificates.json) and [verify_factor_lieb_alternating_eight.py](verify_factor_lieb_alternating_eight.py) describe and verify the identities, one for each \((\lambda,\nu,t)\) of §1,
\[
           \operatorname{per}A-f_{\lambda,t}-S/20
               =\sum_{l=1}^{23} c_l\,G_l(A),\qquad c_l\in\mathbb Q_{>0}.
\tag{2}
\]
Each \(G_l\) is an instance defined in §§2–3 with a literal vector or integer parameters in the JSON. For an ordinary class sum the averaged coefficient is the mean of the real parts over its permutations. For a split coordinate \(J_\nu\) the coefficient is the mean of their imaginary parts times \(\varepsilon(\sigma)\), over the entire ordinary type \(\nu\). Hermitian symmetry pairs the two split classes by inverse, so the latter is exactly the coefficient of \(J_\nu\). Other classes are single even-conjugacy orbits, including odd permutations whose centralizers contain an odd element. For a Gram term the verifier takes a permutation, recovers its two crossing partial bijections, and computes the residual determinant signs when requested. It derives the symmetric-group characters by Frobenius's coefficient formula (Vandermonde times the cycle power sums), not from a supplied character table. All 40,320 permutation coefficients in each identity, both split coordinates, both actual conjugacy splits, and the matching incidences are checked. The expected columns in the JSON are checked against the derived columns, not used as definitions.

Run in ordinary Python 3 with assertions enabled:

~~~sh
python3 verify_factor_lieb_alternating_eight.py
~~~

The two positive decompositions and endpoint interpolation prove the four split cases with the asserted strict deficit. The nonsplit restrictions were reduced in §1. No floating-point arithmetic, sampling or external package is a premise of (2). No conclusion for all order-eight subgroups, for the all-order conjecture, or for the different permanent-on-top question is made. The generalized conjecture is [Lieb's 1966 conjecture](https://doi.org/10.1512/iumj.1967.16.16008).
