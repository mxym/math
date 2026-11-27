# Anisotropic Gaussian kernel smoothing cannot depend only on the smallest width

This note gives a counterexample to the uniform anisotropic bound as stated in Theorem 4.2 and Corollary 4.3 of the 59-page full version of Albrecht, Felderhoff, Lai, Lapiha and Woo, *A Gaussian Leftover Hash Lemma for Modules over Number Fields*. The statements are identified in the [author-hosted document](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf), printed p. 23, and the [fixed manuscript mirror](https://opencryptology.org/2025/1852/versions/20260428T172000Z.pdf) of the [February 24, 2026 ePrint revision](https://eprint.iacr.org/2025/1852). Lemma 4.12 on printed pp. 28–29 has the same anisotropy issue for bounded preimages. We are not making a claim about the condensed proceedings wording, the intended spherical result, or any concrete scheme.

## An anti-concentration observation

Fix a number field \(K\) of degree \(d\), \(r\ge1\), \(m>r\), and let \(X_1,\ldots,X_m\) be independent columns with law \(D_{\mathcal O_K^r,S}\), in the canonical Euclidean norm and with density weight \(\exp(-\pi\|S^{-1}x\|^2)\) on the lattice. Fix any sequence of positive-definite \(S\) for which \(\det S\) tends to infinity. Poisson summation gives
\[
 \max_x\Pr[X_i=x]=\frac1{\rho_S(\mathcal O_K^r)}
          \le\frac{\det\mathcal O_K^r}{\det S}.
\]
Indeed the dual theta expression for \(\rho_S\) has a constant term \(\det S/\det\mathcal O_K^r\) and all terms nonnegative.

For any fixed \(u\in\mathcal O_K^m\setminus\{0\}\) and \(b\in\mathcal O_K^r\), condition on all columns except one with \(u_i\ne0\). The equation \(\sum_j u_jX_j=b\) determines at most one value of the remaining column: multiplication by a nonzero field element is injective. Thus the probability of this equality is at most the displayed maximum atom. For any fixed \(B<\infty\), the set of nonzero integral \(u\) with \(\|u\|\le B\) is finite, so with probability tending to one none obeys the equality. This proves both
\[
 \lambda_1(\ker X\cap\mathcal O_K^m)\ \longrightarrow\infty
 \quad\text{in probability}
\]
and divergence of the length of any preimage for a fixed nonzero \(b\), interpreting a missing preimage as infinite. More quantitatively, a fixed-dimensional lattice has \(O((1+B)^{dm})\) vectors in this ball, by a cube-covering volume bound with any fixed fundamental domain. Thus for any fixed \(0<\delta<1\), one can take \(B=c_\delta(\det S)^{1/(dm)}\) for large \(\det S\) and retain failure probability at most \(\delta\), for a positive constant depending on the fixed lattice and dimensions. Here the real span of the integral kernel has dimension between \(d(m-r)\) and \(dm\), because the kernel is a subspace defined over \(K\) and \(m>r\). For any positive-dimensional rank-\(k\) lattice \(L\), [Banaszczyk's transference inequality](https://doi.org/10.1007/BF01445125) gives \(\lambda_1(L^*)\le k/\lambda_1(L)\). As both signs of a shortest dual vector contribute to the nonzero dual theta mass,
\[
 \eta_\epsilon(L)\ge
 \frac{\sqrt{\log(2/\epsilon)/\pi}}{\lambda_1(L^*)}
 \ge \frac{\sqrt{\log(2/\epsilon)/\pi}}{k}\lambda_1(L),\qquad 0<\epsilon<1.
\]
So the kernel smoothing parameter also tends to infinity in probability, for fixed \(d,r,m,\epsilon\).

## A fixed field and varying covariance

In particular take \(K=\mathbb Q(\zeta_8)\), \(r=1\). Give one entire complex place width \(T\to\infty\) in its two real coordinates and the other fixed width \(s_0>\max(\eta_{1/2}(\mathcal O_K),\sqrt{2\pi d})\). This example is diagonal by canonical places; it does not require a covariance mixing places. Then \(s_{\min}(S)=s_0\) and \(\det S=s_0^2T^2\). Choose any fixed \(\epsilon\in(0,1/2)\) and fixed \(m>r\) large enough for the displayed threshold of AFLLW Theorem 4.2 (or Corollary 4.3), which is independent of \(T\). Every quantity in the claimed upper bound is then fixed, contrary to the divergence proved above. This rules out the uniform \(s_{\min}(S)\)-only bound for the unrestricted \(S\) in Theorem 4.2 and Corollary 4.3 as written. The same fixed-ball argument with \(b=f e_1\) rules out Lemma 4.12's claimed anisotropy-independent short-preimage bound. Fixing \(m\) here is valid for any proposed absolute constant in the sample-threshold bound: first choose such an \(m\), then let \(T\) tend to infinity.

## The corresponding tail mismatch

The related auxiliary Lemma 4.8 also has a narrower defect. Its gain event uses the Euclidean cutoff \(\sqrt{rd}\,s_{\min}(S)\), while its proof invokes \(s_1(S)=s_{\max}(S)\) for the tail. In the example above a fixed-radius ball has probability tending to zero by the maximum atom bound. Given any old columns and no win, the next column is independent of that history; thus the probability of a gain is at most this vanishing ball probability. The conditioning event has positive probability, since all old columns can be zero. An ellipsoid cutoff such as \(\|S^{-1}x\|\le\sqrt{rd}\) addresses this tail mismatch, but does not by itself establish a kernel bound.

The counterexample requires unbounded anisotropy with fixed smallest width. It does not contradict a spherical or bounded-condition-number statement, and it does not establish a replacement upper bound. It uses no concrete scheme, key, modulus, or solver. The supplementary checker verifies synthetic algebraic and normalization identities; none of the proof rests on numerical experiments.
