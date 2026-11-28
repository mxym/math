# Exact relabeling rigidity for any equal number of dyadic ring samples

## 1. Statement

Use the one-row experiment \(P_s\) and notation of the
[fixed single-row theorem at 0493a4bb320cd5e2740381680810b5b326a672d6](https://github.com/mxym/math/blob/0493a4bb320cd5e2740381680810b5b326a672d6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-joint-sample-symmetries.md). Here \(q\ge3\) is odd and \(d\) is a power of two. For each positive integer \(k\), consider \(P_s^{\otimes k}\), where all coefficients and responses are independent conditional on the one shared label \(s\). The width \(0<b<1\) is fixed within the experiment. A candidate Borel kernel can act jointly on all input rows and change all output rows, with no time, memory or causality constraint; the output must have the target law.

**Theorem.** For every finite \(k\ge1\), an exact identity
\[
 P_s^{\otimes k}K=P_{\psi(s)}^{\otimes k}\quad\text{for all }s\in R,
 \tag{1}
\]
where \(\psi:R\to R\) is a permutation and \(K\) is label-independent, is possible exactly for the same maps as in the one-row theorem:
\(\psi(s)=v+u\,\sigma_l(s)\), with \(u\in R^\times,\ v\in R,\ l\in(\mathbb Z/2d)^\times,\ \sigma_l(X)=X^l\).
For each fixed forbidden tuple \((q,d,b,k,\psi)\), the infimum over kernels of the worst-label TV error in (1) is strictly positive. This assertion is pointwise in the parameters, not a uniform bound on their limits.

In addition, when there are fewer input rows than output rows at the same width, exact simulation is impossible for **every** label permutation. The equal-size theorem does not classify transformations that discard rows (\(k\) input rows and fewer output rows). No efficiency or hardness claim about general algorithms or cryptographic schemes is made.

## 2. Posterior distribution under a putative symmetry

Take the uniform prior on \(R\), \(N=|R|\), and write \(\eta_k(Z)\) for the posterior probability vector for the observation \(Z\) of \(k\) rows. The mixture law is \(\mu_k=N^{-1}\sum_sP_s^{\otimes k}\). As in the proof of the one-row theorem, for any exact \(K\) the posterior conditional expectation carries \(\eta_k(Z)\) to \(\psi^*\eta_k(Z')\). The output marginal is again \(\mu_k\), so equality of the mean quadratic norms forces
\[
 \eta_k(Z)=\psi^*\eta_k(Z') \quad\text{almost surely}.
\]
In particular the **law** of \(\eta_k(Z)\) is invariant under \(\psi^*\). Centering logarithms commutes with a label permutation. All entries are positive, so if \(W_k\) denotes the centered log vector, its law is also invariant.

For a coefficient tuple \(\mathbf a=(a_1,\dots,a_k)\), \(W_k=\sum_i W(a_i,y_i)\) with the \(W\) from the one-row theorem. Indeed the log likelihoods add, and uniform averaging over \(s\) kills the common posterior normalization. Put \(h=\log f_b\). For one coefficient \(a\) and coordinate \(j\), write
\[
 c_{a,j}(t)(s)=h(t-(as)_j/q)-\mathbb E_r h(t-(ar)_j/q),
 \qquad W(a,y)=\sum_{j=0}^{d-1}c_{a,j}(y_j).
 \tag{2}
\]
The observations \(y\) have a positive density on the product torus conditional on every coefficient tuple. We next recover a distinguished submeasure directly from the **law** of \(W_k\), without presuming the kernel preserved any coefficient.

## 3. Rank separates one nonzero row from two or more

Let \(\chi_w(s)=e^{2\pi i\langle w,s\rangle/q}\) be the coefficient character, and let \(\bar a=a(X^{-1})\). If \(a\ne0\), all \(2d\) of
\[
  \pm w_j,\quad w_j=\bar a X^j,\quad 0\le j<d
 \tag{3}
\]
are nonzero and distinct. Multiplication by \(X\) is a unit, and \(2\) is invertible, so the only remaining case would require \(\bar a(1\pm X^i)=0\) for some \(0<i<d\). But these binomials are units: set \(m=d/\gcd(i,d)\), which is even, and \(t=\pm X^i\); then \(t^m=-1\) since \(i/\gcd(i,d)\) is odd, and
\[
 (1-t)(1+t+\cdots+t^{m-1})=2 .
\]
For \(d=1\) there are no such pairs. This is where the dyadic restriction enters.

For every \(w_j\) in (3), the real-linear span of the vectors \(c'_{a,j}(t)\) contains both \(\operatorname{Re}\chi_{w_j}\) and \(\operatorname{Im}\chi_{w_j}\). To see this, take the first sine and cosine Fourier moments of (2) as a function of \(t\). The nonzero first Fourier coefficient of \(h\) from (4) of the [one-row theorem](https://github.com/mxym/math/blob/0493a4bb320cd5e2740381680810b5b326a672d6/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-joint-sample-symmetries.md#3-recovering-the-coordinate-subspaces-from-unit-branches) stays nonzero after differentiation; its mean over \(s\) is zero by nontriviality of \(\chi_{w_j}\). This gives precisely the real/imaginary pair up to signs and nonzero factors. The integrals belong to the span since it is a closed subspace of a finite-dimensional vector space. The \(2d\) real spanning witnesses are independent: the \(2d\) complex characters indexed by (3) are orthogonal and each pair has odd order at least three.

It follows that \(W(a,\cdot)\) has derivative rank \(d\) at some point and almost everywhere. In fact the \(d\) columns of its derivative depend separately on the \(d\) coordinates \(y_j\). If all their wedges vanished for all choices, multilinearity would force vanishing for every tuple of vectors chosen from the separate spans. This contradicts the independent tuple of real characters \(\operatorname{Re}\chi_{w_j}\). At least one \(d\times d\) analytic minor is therefore nonidentically zero, so its zero set is null. The span of *all* derivatives of this one row, over all response coordinates and values, has dimension at least \(2d\).

Now take a coefficient tuple with at least two nonzero entries. Place the responses for a first nonzero coefficient at a point of rank \(d\). Some derivative column for a second nonzero coefficient can be placed outside this fixed \(d\)-dimensional span, since the latter row's total derivative span has dimension at least \(2d\). Thus the full sum map has rank at least \(d+1\) somewhere, and an analytic minor proves rank at least \(d+1\) almost everywhere on the response torus. Other rows, including any zero coefficients, do not change these chosen derivative columns.

## 4. Extract the low-dimensional law

Any coefficient tuple with at most one nonzero entry contributes a centered log vector in the fixed compact set
\[
 C_{\rm low}=\{0\}\cup\bigcup_{a\ne0}W(a,\mathbb T^d).
\]
This has \((d+1)\)-dimensional Hausdorff measure zero, because it is a finite union of Lipschitz images of compact \(d\)-dimensional manifolds and a point. In contrast, the law from any coefficient tuple with at least two nonzero entries gives zero probability to *every* set of \((d+1)\)-dimensional Hausdorff measure zero. Indeed at a regular response choose \(d+1\) target coordinates whose projected derivative has rank \(d+1\); locally the map to them is a submersion. The coordinate projection of any such Hausdorff-null target set is Lebesgue-null, and its preimage is null by the submersion coordinates and Fubini. A countable covering of the regular set and its null complement prove the claim. Absolute continuity in response coordinates ensures the same null sets conditional on the chosen coefficients.

Consequently the centered-log law decomposes uniquely as a sum of the submeasure from zero or one nonzero coefficient, supported on a \((d+1)\)-null set, and a submeasure that vanishes on all such sets. To see uniqueness directly, restrict both decompositions to the union of the two candidate null supports. A coordinate permutation of the posterior is an orthogonal map of the centered-log space and hence preserves these null sets. Therefore invariance of the total law from Section 2 implies invariance of its low-dimensional submeasure.

The all-zero coefficient tuple has probability \(N^{-k}\) and contributes an atom at \(0\). The tuples with exactly one nonzero coefficient have total mass \(k(1-1/N)N^{-(k-1)}\) and, conditional on that event, the law is the one-row centered-log law given \(A\ne0\). This follows from iid uniform coefficients and the independence of all zero-coefficient responses; those responses contribute exactly zero to the centered log. Subtract the all-zero atom, divide by the positive one-nonzero mass, and restore the one-row atom of mass \(1/N\). This proves invariance of the one-row centered-log law under \(\psi^*\). Exponentiation and normalization recover the posterior vector and commute with \(\psi^*\), so the single-row posterior law is invariant as well. In particular the single-row support inclusion of Sections 2–5 of the fixed theorem holds. That theorem now yields the claimed form of \(\psi\). Conversely its allowed deterministic one-row map can be applied independently to each row and preserves their conditional iid structure.

## 5. Stability and the unequal-size impossibility

Let \(\mathcal L_k\) be the law of \(\eta_k(Z)\) under the uniform prior and \(\mu_k\). The previous argument showed that \(\mathcal L_k\) is invariant under \(\psi^*\) only for the allowed permutations, independently of the existence of a kernel. Let \(W_2\) denote the Wasserstein distance using the ordinary Euclidean distance on the simplex. Every kernel with worst-label error \(\delta\) in (1) satisfies
\[
 \delta\ge\frac18 W_2\bigl(\mathcal L_k,\psi^*\mathcal L_k\bigr)^2 .
 \tag{4}
\]
Indeed compare the simulated and target joint laws of \((S,Z')\), within \(\delta\) in TV. The bounded quadratic prediction loss for the target posterior \(\psi^*\eta_k(Z')\) differs by at most \(2\delta\). The same orthogonality as in the one-row theorem says that the loss excess over the initial Bayes risk is \(\mathbb E\|\eta_k(Z)-\psi^*\eta_k(Z')\|^2\). Thus this coupling costs at most \(2\delta\) in squared Wasserstein distance. The simulated marginal of \(Z'\) is within \(\delta\) in TV of \(\mu_k\), so a second coupling between its transformed posterior and the target transformed posterior costs at most \(2\delta\) (the squared diameter of a probability simplex is 2). The triangle inequality for \(W_2\) proves (4). For a forbidden permutation the two laws differ, so the bound is positive. It can be small, since the distinguished one-nonzero part itself loses mass rapidly with \(k\).

Finally let \(I_j=\mathbb E\|\eta_j\|_2^2\). Fresh rows give a posterior martingale:
\[
 I_{j+1}-I_j=\mathbb E\|\eta_{j+1}-\eta_j\|_2^2>0 .
\]
For strictness, every earlier history has positive posterior weights for all \(s\), and the next coefficient has positive probability of being \(1\). Then the response family is not constant in \(s\), so its Bayes update is nonconstant with positive probability; otherwise, with all prior weights nonzero, equality of the updated and old vectors would force all conditional densities to agree almost everywhere. A Markov transition cannot increase the mean posterior squared norm, while permuting the label does not change \(I_j\). Thus it cannot take \(j\) rows exactly to any larger number at the same width. This last argument also holds without the dyadic assumption.

The result is a theorem about exact experiments and the specific positive noise family. It does not describe sample-preserving search-to-decision in a model with oracle calls and changed target distributions, a practical solver, or a scheme. Its new ingredient over the one-row theorem is the rank/null-measure separation in Sections 3 and 4. The companion verifier covers finite modular witnesses and supporting probability identities, not the analytic submersion proof.
