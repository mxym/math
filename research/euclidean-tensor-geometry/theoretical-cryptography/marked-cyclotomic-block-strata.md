# The block-separability strata of a marked cyclotomic ideal lattice

**Scope.** Exact orthogonality of additive direct-sum coordinates and Gaussian product structure on one abstract ideal lattice. No computational claim about recovering lattice elements or secrets, and no assessment of a cryptosystem.

## 1. Setup and classification

Fix \(m>2\), \(K=\mathbb Q(\zeta_m)\), \(R=\mathcal O_K\), and a nonzero fractional ideal \(I\) of \(R\). At the embeddings \(\sigma:K\hookrightarrow\mathbb C\), choose positive **squared** metric weights \(w_\sigma\) equal at conjugate embeddings. Equip \(I\) with
\[
 \langle x,y\rangle_w=\sum_\sigma w_\sigma\,\sigma(x)\overline{\sigma(y)}.
\]
It is a real positive inner product. Both \(I\) and this metric remain marked: multiplication by \(\zeta_m\) is a specified isometry. Let \(D\) be the number of summands in the unique maximal integral orthogonal decomposition of this lattice. A *cyclic \(r\)-split* is an orthogonal direct sum into \(r\) nonzero sublattices which multiplication by \(\zeta_m\) permutes as a cycle.

**Classification.** The following hold.

* \(D\mid m/\operatorname{rad}(m)\). For \(r\mid m\), a cyclic \(r\)-split exists exactly when \(r\mid D\); when it exists it is unique as a partition into sublattices. Ordinary orthogonal sums into arbitrarily grouped blocks need not be cyclic.
* Fix \(r\mid m/\operatorname{rad}(m)\), put \(F_r=\mathbb Q(\zeta_m^r)\), and write \(R_r=\mathcal O_{F_r}\). For these \(r\) the existence of a cyclic \(r\)-split is equivalent to
  \[
   I=\alpha J R\quad(\alpha\in K^\times,\ J\text{ a fractional }R_r\text{-ideal}),\qquad
   w_\sigma|\sigma(\alpha)|^2\text{ constant on each fiber }\sigma|_{F_r}=\tau.
                                                        \tag{1}
  \]
  The blocks are \(\alpha\zeta_m^j J\) for \(0\le j<r\). Under the identification with \(J\), each block has weights \(r\,w_\sigma|\sigma(\alpha)|^2\) on the embeddings of \(F_r\).
* The \(r\)-split condition for a fixed \(I\), as the normalized log metric varies modulo multiplication by units, is a disjoint union of parallel embedded subtori indexed by
  \[
     \{[J]\in\operatorname{Cl}(F_r):[JR]=[I]\}.
                                                        \tag{2}
  \]
  If nonempty, it has exactly \(|\ker(\operatorname{Cl}(F_r)\to\operatorname{Cl}(K))|\) connected components. On degree-zero Arakelov class groups the corresponding extension is injective, even when extension of ordinary ideal classes is not injective.

The constraint on attainable numbers of blocks is already known in the unmarked classification of cyclotomic ideal lattices (see §6). Here the ideal, metric and multiplication action are fixed, which is essential in (1) and (2).

## 2. Why the arithmetic and metric conditions are necessary

In any positive definite lattice, call a nonzero vector indivisible orthogonally if it is not a sum of two nonzero orthogonal lattice vectors. Such vectors generate: repeatedly split a divisible vector, with strictly decreasing squared lengths, and use finiteness in bounded balls. Connect two such vectors when their inner product is nonzero. The different graph components generate pairwise orthogonal sublattices, whose direct sum is the whole lattice. In any orthogonal direct sum an indivisible vector lies wholly in one block, and connected vertices lie in the same block. Thus these sublattices are exactly the unique finest blocks.

Multiplication by \(\zeta_m\) permutes them. It acts irreducibly on \(I\otimes_{\mathbb Z}\mathbb Q=K\), with characteristic polynomial \(\Phi_m\). The sum of any orbit of blocks would span a stable rational subspace; hence there is one orbit, a \(D\)-cycle. Labeling the finest blocks by \(\mathbb Z/D\mathbb Z\), any cyclic \(r\)-split is an equivariant quotient to \(\mathbb Z/r\mathbb Z\), so \(r\mid D\) and the partition is the congruence classes modulo \(r\).

For a cyclic \(r\)-split write the first block as \(I_0\). Its rational span is stable under \(\zeta_m^r\) and hence is a vector space over \(F_r\). Its rational dimension is \([K:\mathbb Q]/r\). On the other hand \(K/F_r\) has degree at most \(r\) because \(\zeta_m\) satisfies \(T^r-\zeta_m^r\). Both inequalities must be equalities: \([K:F_r]=r\), and \(I_0\otimes\mathbb Q=\alpha F_r\) for some \(\alpha\in K^\times\). Since a cyclic permutation has order dividing \(m\), \(r\mid m\). The equality \(\varphi(m)=r\varphi(m/r)\) is equivalent to keeping every prime divisor of \(m\) in \(m/r\), by Euler's product formula. This is exactly \(r\mid m/\operatorname{rad}(m)\).

Now \(I_0=I\cap\alpha F_r\), since the rational spans of the orthogonal blocks are a direct sum. The right side is stable under multiplication by \(R_r\). Thus \(J=\alpha^{-1}I_0\) is a fractional \(R_r\)-ideal. The powers \(1,\zeta_m,\ldots,\zeta_m^{r-1}\) are an \(R_r\)-basis of \(R\): linear independence follows from the degree, and all powers reduce using \(\zeta_m^r\in R_r\), while \(\mathbb Z[\zeta_m]=R\). Consequently the additive sum of the cyclic translates of \(I_0\) is exactly \(\alpha J R\).

Write \(d_\sigma=w_\sigma|\sigma(\alpha)|^2\). For the rational spans of two proposed blocks at difference \(k\), their pairing reduces, using vectors of \(F_r\), to the coefficients
\[
    c_{\tau,k}=\sum_{\sigma|_{F_r}=\tau} d_\sigma\,\sigma(\zeta_m)^k .
                                                        \tag{3}
\]
The spans at differences \(k=1,\ldots,r-1\) are all orthogonal exactly when each \(c_{\tau,k}=0\) there. To see necessity, the pairings with \(1\) in one block and arbitrary \(f\in F_r\) in the other yield \(\sum_\tau \tau(f)c_{\tau,k}=0\); the real embedding space of \(F_r\) is spanned by those \(f\). Real embeddings have real coefficients and conjugate embeddings have conjugate coefficients, so the pairing is nondegenerate. Over each \(\tau\), the \(r\) values of \(\sigma(\zeta_m)\) are all \(r\) roots of \(\tau(\zeta_m^r)\). Equation (3), divided by an appropriate root phase, is the Fourier transform of the \(r\) weights. The nonconstant coefficients vanish exactly when those weights are constant. This proves necessity and sufficiency of (1), and summing the \(r\) equal weights gives the block metric.

## 3. The marked log tori and ideal-class fibers

Let \(V_K\) be the space of real conjugation-symmetric embedding vectors with coordinate sum zero. Define the centered log map
\[
 \ell_K(a)_\sigma=2\log|\sigma(a)|
        -\frac{2}{[K:\mathbb Q]}\sum_\nu\log|\nu(a)| .
\]
Global scaling of metric weights can be discarded. A normalized \(\log w\in V_K\) varies on the marked torus \(T_K=V_K/\ell_K(R^\times)\), since changing the ideal coordinates by multiplication with a unit shifts the log metric by its log vector. Identify \(V_{F_r}\) with the subspace of \(V_K\) obtained by repeating coordinates across embedding fibers.

First note a rigidity consequence of uniqueness in §2. If \((a)R=JR\) for some \(a\in K^\times\), and \(a\overline a\in F_r\), then \(a=\zeta_m^j b\) for some \(b\in F_r^\times\) and \(J=(b)R_r\). In fact \(JR\) has its standard \(r\)-split \(J,\zeta_mJ,\ldots\) for the spherical metric. Multiplication by \(a\) gives another \(r\)-split of the same lattice from the standard split of \(R\), because \(|\sigma(a)|^2\) is constant on fibers. Uniqueness gives \(aR_r=\zeta_m^j J\) for some \(j\), proving the assertion. The equivalence of constant absolute square on fibers and \(a\overline a\in F_r\) follows by applying the Galois group of \(K/F_r\) and using injectivity of an embedding. Taking \(a\) to be a unit gives the exact lattice intersection
\[
        \ell_K(R^\times)\cap V_{F_r}=\ell_{F_r}(R_r^\times)
                           \quad\text{under the embedding of log spaces}. \tag{4}
\]
For the inclusion that uses rigidity, \(J=R_r\), so the resulting \(b\) is a unit of \(R_r\). Thus \(T_{F_r}\) embeds as a genuine subtorus, without an extra finite unit quotient.

For a class in (2), choose \(J\) and \(\alpha\) with \(I=\alpha JR\). By (1) its locus in \(T_K\) is
\[
                      -[\ell_K(\alpha)]+T_{F_r}.
\]
A generator change by a unit, or a change of \(J\) within its class, changes this expression only by a log-unit vector or an element of \(V_{F_r}\). If two such cosets meet, absorb the unit-lattice discrepancy into the chosen generators. At that same metric they give the same partition into \(r\) blocks, so for some \(j\),
\(\alpha_1 J_1=\zeta_m^j\alpha_2 J_2\). Comparing rational spans shows \(\zeta_m^j\alpha_2/\alpha_1\in F_r^\times\), so the two classes are equal. This proves (2) and the component count.

More intrinsically, use degree-zero Arakelov pairs \((J,u)\), with \(u_\tau>0\) constant on conjugate embeddings, \(N(J)\prod_\tau u_\tau=1\), and the equivalence
\((J,u)\sim(b^{-1}J,u|\tau(b)|)\). The squared weights are \(u_\tau^2\). Extending the ideal to \(R\) and repeating the \(u_\tau\) gives a continuous homomorphism \(\operatorname{Pic}^0(F_r)\to\operatorname{Pic}^0(K)\): both factors of the degree-zero normalization are raised to the \(r\)-th power. If a class is in the kernel, the extended ideal is \((a)R\) with \(u_\tau|\sigma(a)|=1\) across each fiber. The rigidity above recovers a generator in \(F_r\), giving triviality of the original class. By (1), the image is exactly the cyclic \(r\)-split locus. These are assertions about marked Arakelov classes, not quotienting further by arbitrary isometries or embedding permutations.

For two admissible divisors \(r,s\), the intersection of their loci is exactly the locus for \(h=\operatorname{lcm}(r,s)\), because \(r\) and \(s\) must both divide the finest block count. Each component labeled by \([J_h]\) on the intersection lies in the components labeled by the extensions to \(F_r,F_s\), respectively; this follows by grouping the \(h\)-blocks. In particular two specified labeled subtori intersect exactly in the union of \(h\)-components with those two class extensions.

There is also a separation interpretation. Let \(\Gamma_{\rm rel}\) be the orthogonal projection of \(\ell_K(R^\times)\) to \(V_{F_r}^\perp\) inside \(V_K\). This is a lattice because \(V_{F_r}\) is a rational subspace relative to the log-unit lattice by (4) and Dirichlet's unit theorem. If \(\kappa=\ker(\operatorname{Cl}(F_r)\to\operatorname{Cl}(K))\), taking the log of a generator of an extended principal ideal gives a homomorphism \(\kappa\to V_{F_r}^\perp/\Gamma_{\rm rel}\). Changes of representative and of generator do not change its class. It is injective by generator rigidity. As ideal norm annihilates the kernel by \(r\), distinct components have distance at least \(\lambda_1(\Gamma_{\rm rel})/r\) in the quotient Euclidean metric, when there is more than one component. This statement uses the class group only as a label, and does not presume that its kernel is nontrivial for every tower.

## 4. A finite metric bound away from the strata

The algebraic condition \(I=\alpha JR\) makes sense without orthogonality. If it holds, it gives cyclic additive blocks, whose real spans are orthogonal exactly at the corresponding locus. For \(r>1\) set
\[
 \rho=\max_{\tau,\ 1\le k<r}\frac{|c_{\tau,k}|}{c_{\tau,0}},\qquad
 \Delta=\max_\tau\log\frac{\max_{\sigma|\tau}d_\sigma}
                            {\min_{\sigma|\tau}d_\sigma}.
\]
Here \(\rho\) is precisely the largest absolute normalized cross-pairing among two different blocks (supremum over unit vectors in their real spans). Indeed the intrablock metric has weights \(c_{\tau,0}\), and the cross-block multiplier has absolute value \(|c_{\tau,k}|\); selecting one real or one complex-conjugate coordinate pair attains the maximum. In a real fiber the coefficient is real, ensuring the same formula.

With \(p_\sigma=d_\sigma/\sum_{\nu|\tau}d_\nu\) in each fiber, Fourier inversion gives \(|r p_\sigma-1|\le(r-1)\rho\). Conversely every nonconstant Fourier coefficient of \(p\) is bounded by \(\sum_\sigma|p_\sigma-1/r|\). These yield
\[
     \frac{\tanh(\Delta/2)}{r-1}\ \le\ \rho\
                      \le\ \min(1,e^\Delta-1).          \tag{5}
\]
For the lower bound, if \((r-1)\rho<1\) divide the maximum possible \(r p_\sigma\) by its minimum; the resulting ratio is at most \((1+(r-1)\rho)/(1-(r-1)\rho)\). If \((r-1)\rho\ge1\) the claim is automatic. The upper bound uses \(r p_\sigma\in[e^{-\Delta},e^\Delta]\). Thus a small coupling in a proposed cyclic decomposition is equivalent, up to explicit constants, to a small within-fiber logarithmic variation of the weighted embedding norm of its generator. The spread \(\Delta\) is the norm of the log-weight offset in the quotient \(V_K/V_{F_r}\) defined by the maximum within-fiber range. Minimizing over the cosets labeled in (2) and over possible unit translates gives the same two-sided bound for the best cyclic additive decomposition, with \(\Delta\) replaced by the log distance to the \(r\)-split locus in that spread norm. The log-distance minimum is attained since the projected unit lattice is discrete and there are finitely many ideal labels. This does not assert attainment of the correlation infimum for every off-locus width. If (2) is empty, there is no cyclic additive decomposition of that size.

## 5. Consequences and examples

1. For a spherical ring of integers, \(\alpha=1,J=R_r\) works for every admissible \(r\). Its finest count is \(m/\operatorname{rad}(m)\) and each block has rank \(\varphi(\operatorname{rad}(m))\). Its Euclidean dual has the same finest count, since duality preserves every orthogonal sum and is involutive. The squarefree indecomposability conclusion is the known special case.
2. Spherical block splitting does not require the ideal to be principal. For example take \(F=\mathbb Q(\zeta_{23})\) and \(K=\mathbb Q(\zeta_{23^2})\). An ideal class of order \(3\) in \(F\) exists (see the class group in [Long, Table 2.1](https://www2.math.upenn.edu/grad/dissertations/JingLongThesis.pdf)); it remains nontrivial after extension of degree \(23\) because composing extension with norm is the \(23\)-rd power. The extended ideal is nonprincipal and spherical, with exactly \(23\) orthogonal blocks of rank \(22\).
3. For the fixed \(I\) and \(m>4\), all \(r>1\) images, if nonempty, have smaller log dimension than \(T_K\). Indeed \(F_r\) has smaller degree and is either CM or \(\mathbb Q\); the equality of unit ranks in a quadratic CM extension of a totally real field causes no exception here other than \(m=4\) and its rank-zero tori. Hence almost all log metrics on a fixed \(I\) are indecomposable, even when the spherical metric is highly decomposable.
4. For any given additive lattice direct sum and any real center, the discrete-Gaussian law for the specified quadratic form splits into independent summands on those coordinates if and only if the sum is orthogonal. Sufficiency is the factorization of its weight. For necessity compare the ratio of the weights at \(x+y,x,y,0\), with \(x,y\) in different summands; the log ratio for positive weights is minus twice the bilinear cross term (with the usual common Gaussian exponent scale). Independence makes it zero. The classification concerns existence of product coordinates in the supporting lattice, not convolution factorizations into arbitrary positive laws.

There is a simple arithmetic obstruction for metrics \(w_\sigma=\sigma(\beta)\) with totally positive \(\beta\in K^+\). By (1) a split requires \(\beta\alpha\bar\alpha\in F_r\). If \(F_r\) is CM this positive element lies in \(F_r^+\), and
\[
     N_{K^+}(\beta)N_K(I)
        =N_{K^+}(\beta\alpha\bar\alpha)\,N_{F_r}(J)^r
        =\big(N_{F_r^+}(\beta\alpha\bar\alpha)\,N_{F_r}(J)\big)^r .
\]
Thus the product of ideal norm and metric norm must be an \(r\)-th power of a positive rational. If \(F_r=\mathbb Q\), the analogous necessary exponent is \(r/2\).

This is sharp for spherical powers \(I=\mathfrak P^e\) of the unique prime above \(p\) in \(m=p^a\), where \(N(\mathfrak P)=p\) and \(e\in\mathbb Z\). If \(F_r\) is CM, the condition is \(r\mid e\) and is sufficient by base extension from the corresponding power of the prime of \(F_r\), since relative ramification index is \(r\). Thus for odd \(p\), the finest count is \(p^{\min(a-1,v_p(e))}\), using \(v_p(0)=+\infty\). For \(p=2\), \(a\ge2\), the sole admissible real base is \(F_r=\mathbb Q\) at \(r=2^{a-1}\), which requires \(r/2\mid e\). It is sufficient because \(1+i\) generates \(\mathfrak P^{r/2}\) in \(K\) and its absolute square is rational; negative powers are allowed. Therefore in the dyadic case the finest count is \(2^{a-1}\) if \(2^{a-2}\mid e\), and otherwise \(2^{v_2(e)}\). These norm and block-count conclusions are distinct from shortest-shell smoothing estimates for the same dyadic ideals.

## 6. Primary references and distinction

[Alexandre Lemire Paquin, *Ideal Lattices in Cyclotomic Fields*, Lemma 4.2.4 and Proposition 4.2.5](https://central.bac-lac.gc.ca/.item?app=Library&id=TC-QMM-123244&oclc_number=911042918&op=pdf) already classifies the possible counts and isometry types for unmarked decompositions and explicitly includes the squarefree obstruction. [Liu–Liang–Ding, *Dimension Reduction for Theta Series of Ideal Lattices*](https://eprint.iacr.org/2026/2028) use exact block diagonality to factor theta weights in relative coordinates. [Schoof, *Computing Arakelov Class Groups*](https://library.slmath.org/books/Book44/files/14schoof.pdf) gives the marked ideal-lattice model of the degree-zero Arakelov class group. The additional results here are the fixed-ideal/fixed-metric arithmetic criterion, exact labeled log-unit strata and their intersection law, the balanced-generator rigidity and its consequences for capitulation, and the finite correlation bound (5). Earlier repository work on orthogonal integer coordinates concerns rank-one blocks; the present classification permits blocks of arbitrary equal rank. No assertion about unmarked isometry uniqueness or priority beyond the comparisons is made.

The adjacent checks test exact cyclotomic trace identities and Fourier coefficients on small generated fields. They report 802,987 exact and 5,670 numerical checks. The log-torus and ideal-class statements are proved algebraically, not inferred from those checks.
