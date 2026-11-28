# Correlated wrapped noise: a shifted statistical window with a surviving coordinate-degree barrier

Independent coefficients are not essential to a low-coordinate-degree obstruction in broad ring learning. For one genuinely nonproduct wrapped Gaussian family, the obstruction persists even though the full noise law can be asymptotically singular to the independent-coordinate approximation. The statistical transition has a computable positive displacement from a nearest-neighbor Fourier shell, despite having the same leading-order location.

## 1. Model and main results

Let \(q\ge3\) be any fixed odd integer, \(d\to\infty\) dyadic, and \(R=(\mathbb Z/q)[X]/(X^d+1)\). Let \(U\) be signed cyclic shift on the real power basis, so \(U^d=-I\); take fixed \(0<\rho<1/2\), \(\delta=1-2\rho\), and the positive definite matrix
\[
 C_\rho=I+\rho(U+U^\top).
\]
Fix \(b=\beta/d\), \(\beta>0\). In each row use the wrapped Gaussian density
\[
 f(y)=\sum_{v\in\mathbb Z^d} b^{E(v)}e^{2\pi i v\cdot y},
 \qquad E(v)=v^\top C_\rho v .
\]
This is the wrap of a real Gaussian with covariance \((-\log b) C_\rho/(2\pi^2)\). It has one-coordinate density \(f_b^{(1)}(x)=\sum_{h\in\mathbb Z}b^{h^2}e^{2\pi i h x}\), but its coefficients are not independent. Independent rows \(A_i\) are uniform in \(R\); given one common uniform label \(S\in R\), take \(Y_i=A_iS/q+E_i\) modulo the coefficient torus, with independent errors of density \(f\) across rows. Here \(T\) is the number of rows and \(t_d=Tb^2\to t>0\). Let \(P_{Y\mid A}\) be the mixture law at a fixed public design.

Let \(g\) be the uniform \(q\)-grid shift average of \(f\) within one row, \(Q=g^{\otimes T}\), and let \(\lambda\) be product Haar for all \(Td\) coordinates. Define \(C_d=D(f\|g)\) using natural logarithms. Then
\[
 C_d=d b^2+d b^{2+2\delta}(1+o(1)),                             \tag{1}
\]
and with \(B=\log q\),
\[
 \mathbb E_A\left|
  \operatorname{TV}(P_{Y\mid A},Q)-
     \Phi\!\left(\frac{T C_d-dB}{\sqrt{2t_d d}}\right)
 \right|\longrightarrow0.                                      \tag{2}
\]
The same conclusion holds with reference \(\lambda\) instead of \(Q\). Thus if \(\sqrt d(t_d-B)\to\xi\) is finite, the ordinary independent-noise profile is unchanged when \(\delta>1/4\). At \(\delta=1/4\) it is displaced to \(\Phi((\xi+B\sqrt\beta)/\sqrt{2B})\); for \(\delta<1/4\) the same nominal window has TV tending to 1. At any fixed \(\rho\), (2) is centered at the exact \(C_d\), not at an uncontrolled further truncation of (1).

For an integer \(D\), let \(\Pi_{\le D}\) be the coordinate-degree projection in \(L^2(\lambda)\), and put \(F_A=dP_{Y\mid A}/d\lambda\), \(G=dQ/d\lambda\). For any fixed \(\alpha>0\) satisfying
\[
 K_t(\alpha)=\max_{0\le x\le\alpha}x(1+\log(2t/x))<B
\]
(with value 0 at \(x=0\)), there exists \(c>0\) such that
\[
 \mathbb E_A\|\Pi_{\le\lfloor\alpha d\rfloor}(F_A-G)\|_2^2
 \le e^{-cd}.                                                    \tag{3}
\]
This holds on both sides of the statistical transition; in particular fixed \(t>B\) permits a positive \(\alpha\). The same order bound holds for the projection of the field \(\mathbb E_S h(S)\,dP_{Y\mid A,S}/d\lambda\), for any centered unit-\(L^2\) label feature \(h\) prescribed independently of \(A\). Replacing \(G\) by 1 in (3) adds a vanishing, not in general exponentially small, term. These are bounds on low-coordinate-degree mean tests and do not classify arbitrary algorithms.

For comparison, if \(\rho>1/4\) (equivalently \(\delta<1/2\)), the \(T\)-row error law \(f^{\otimes T}\) and the law of all independent scalar errors with the **same** marginal \(f_b^{(1)}\) have TV tending to 1. The obstruction (3) is therefore not proved by replacing the correlated observations with a TV-close independent model.

## 2. Energies and elementary support components

The quadratic form has the identity
\[
 E(v)=\delta\|v\|^2+\rho\|(I+U)v\|^2.                           \tag{4}
\]
On the cycle of \(d\) coordinate positions, a support other than the full cycle decomposes into disjoint connected intervals separated by empty positions. Energy is additive across these components. A one-site component at integer \(m\ne0\) has energy \(m^2\). A proper interval component of length \(\ell\ge2\) has energy at least \(\delta\sum m_j^2+2\rho\), since each endpoint contributes an integer of absolute value at least 1 to a boundary term of \((I+U)v\). For length two the minimum energy \(2-2\rho=1+\delta\) is attained exactly by the two signed patterns of magnitudes 1 with cancellation at the internal edge. This includes the opposite sign convention on the wrap edge. Other sign choices on those magnitudes have energy \(2+2\rho\); if the magnitudes differ from \((1,1)\), the bound in (4) is at least \(1+4\delta\). There are exactly \(2d\) minimizing adjacent patterns for dyadic \(d\ge4\).

Here are useful weighted counting estimates. For a fixed \(h>0\) and \(0\le z\le1\), let
\[
 \Theta_h(z)=\sum_{v\in\mathbb Z^d} b^{h E(v)}z^{\mathrm{wt}(v)}.
\]
The sum of single-component weights for one-site supports is \(2d z b^h+O(d b^{4h})\). Applying (4) and summing a geometric series, the total for all proper components of length at least two is
\[
 \sum_{\ell=2}^{d-1} O\left(d\, b^{2h\rho}
       \left(\sum_{m\ne0} b^{h\delta m^2}\right)^\ell\right)
       =O\left(d b^{h(1+\delta)}\right).                         \tag{5}
\]
If the sum starts at length 3 it is \(O(d b^{h(1+2\delta)})\). The total of full-cycle supports is at most \((\sum_{m\ne0}b^{h\delta m^2})^d\), negligible at every polynomial scale. Dropping the incompatibility of distinct components, a partition for sets of components is at most the exponential of their total weight; if one nontrivial component is required, mark it and multiply its activity sum by that bound. In particular
\[
 \Theta_h(z)\le
 \exp\{2d z b^h+O(d b^{4h}+d b^{h(1+\delta)})\}
             +O((3b^{h\delta})^d).                            \tag{6}
\]
For \(h=2\) the total component activity is \(O(db^2)=o(1)\). Therefore the partition omitting every vector consisting of a single \(\pm1\) site is at most
\[
 1+O\big((db^2)^2+d b^{2+2\delta}\big).                         \tag{7}
\]
Indeed at least two components cost \(O((db^2)^2)\); the remaining single component is either a longer one or a one-site magnitude at least 2. No independence of the signs on a full-cycle component is assumed.

Denote by \(f_0=\prod_{j=1}^d f_b^{(1)}(y_j)\) the independent reference within a row. On supports with no adjacent nonzero positions the Fourier coefficients of \(f\) and \(f_0\) are equal exactly. With \(b=\beta/d\), the estimates for configurations with an adjacent pair give
\[
 \|\Delta\|_\infty=O(d b^{1+\delta})=o(1),\qquad
 \|\Delta\|_2^2=O(d b^{2+2\delta}),\qquad \Delta=f-f_0.           \tag{8}
\]
For the first bound use the \(h=1\) component activity, whose exponential remains bounded because \(db=O(1)\); for the second use \(h=2\) and Parseval on Fourier coefficients of the difference. The independent model on the affected supports has total squared-coefficient mass only \(O(d b^4)\) (apply the same marked-component count with diagonal energy). Also \(f_0\) is bounded above and away from zero uniformly because \(\log f_b^{(1)}=O(b)\) and \(db=O(1)\), hence so is \(f\).

More sharply, let \(D_{\mathrm{edge}}\) be the function retaining just the \(2d\) Fourier coefficients of \(f\) on the minimizing length-two patterns. Then
\[
 \|D_{\mathrm{edge}}\|_2^2=2d b^{2+2\delta},\qquad
 \|\Delta-D_{\mathrm{edge}}\|_2=o(\sqrt d\,b^{1+\delta}).         \tag{9}
\]
To see the little-oh, a marked adjacent component of length at least three has the strictly smaller activity in (5). For length two, opposite parity of signs from the minimum or magnitudes other than \((1,1)\) have a fixed energy gap by (4). Any extra component beyond an edge dipole has total relative cost \(O(db^2)\) for squared coefficients. The independent-model difference just noted is negligible because \(\delta<1\). Parseval combines these contributions.

## 3. The first correlation contribution to entropy

Write \(D(\cdot\|1)\) for divergence to Haar on one row. Each coordinate marginal of \(f\) is \(f_b^{(1)}\), so
\[
 D(f\|1)=dD(f_b^{(1)}\|1)+D(f\|f_0).
\]
The scalar term is \(b^2+O(b^4)\), by the cosine expansion of \(f_b^{(1)}\log f_b^{(1)}\) and disappearance of the cubic cosine integral. By \(\int\Delta=0\) and the uniform bounds of (8),
\[
 D(f\|f_0)=\tfrac12\int\frac{\Delta^2}{f_0}
                    +O(\|\Delta\|_\infty\|\Delta\|_2^2).        \tag{10}
\]
We may replace \(\Delta\) by \(D_{\mathrm{edge}}\) in the main term using (9) and the bounded reciprocal of \(f_0\). Under Haar, \(D_{\mathrm{edge}}/b^{1+\delta}\) is a sum of bounded centered cosine functions, one per edge, depending only on the two endpoint variables. Its fourth moment is \(O(d^2)\): in the expansion, an edge index isolated from all others, counting repeated indices as nonisolated, gives zero, and the nonzero terms are bounded by the count of up to two connected groups of at least two edge-index occurrences. Thus \(\|D_{\mathrm{edge}}\|_4^2=O(d b^{2+2\delta})\). The product density has \(\|f_0-1\|_2=O(\sqrt d\,b)=o(1)\), so the same is true for \(1/f_0-1\). Hölder gives
\[
 \int D_{\mathrm{edge}}^2(1/f_0-1)=o(d b^{2+2\delta}).
\]
Therefore (10) is \(d b^{2+2\delta}(1+o(1))\). The grid average \(g\) retains exactly the Fourier frequencies in \(q\mathbb Z^d\); it is the same series with parameter \(b^{q^2}\). Equations (5)–(6) give
\[
 \|g-1\|_\infty=O(d b^{q^2}),\qquad
 \|g-1\|_2^2=O(d b^{2q^2}).
\]
Since \(\log g\) is grid-invariant, \(\int f\log g=\int g\log g\). Thus \(D(f\|g)=D(f\|1)-D(g\|1)\) and the last divergence is \(O(d b^{2q^2})\). This proves (1). The reference \(Q=g^{\otimes T}\) is TV-close to \(\lambda\) because its squared \(L^2\) distance to 1 is
\((1+\|g-1\|_2^2)^T-1=O(T d b^{2q^2})=o(1)\).

## 4. Fourier coordinate-degree bound

Use the coefficient-dot pairing on \(R\). As \(U\) is signed shift, multiplication by any \(a\) is adjoint to multiplication by \(\bar a=a(X^{-1})\). At integer frequency vector \((v_i)_{i\le T}\), the Fourier coefficient of \(F_A\) is
\[
 b^{\sum_i E(v_i)}\,\mathbf1_{\{\sum_i\overline A_i(v_i\bmod q)=0\}} .
\]
For \(G\) it is the same weight with the indicator that every \(v_i\) is zero modulo \(q\). Under product Haar, the orthogonal coordinate-degree projection corresponds exactly to keeping Fourier vectors with scalar coordinate support \(\sum_i\mathrm{wt}(v_i)\le D\). The difference has no contributions from the all-zero-mod-\(q\) case. For any other vector, with nonzero ideal \(J=\sum_i (v_i\bmod q)R\), the sum of random coefficient products is uniform on \(J\), so the survival probability is \(1/|J|\).

For the full ideal \(J=R\), the expected projected square is bounded, for each fixed \(0<z\le1\), by \(q^{-d}z^{-D}\Theta_2(z)^T\), by Parseval and a support mark. Since \(Tb^2\to t\), its log upper rate divided by \(d\) is at most \(-B-\alpha\log z+2tz\) for \(D=\lfloor\alpha d\rfloor\). Optimize using \(z=\min(1,\alpha/(2t))\), giving \(K_t(\alpha)-B\). The leading log rate of this full-ideal part is also attained by using no more than one signed unit coordinate per active row: frequencies with \(j\) such rows have weight \((2d b^2)^j\binom{T}{j}\) and generate \(R\). For any fixed \(j/d\to x\in(0,\alpha)\), use \(T=\Theta(d^2)\) and Stirling to obtain \(x(1+\log(2t/x))-B\); approach an endpoint from inside if necessary.

For proper nonzero \(J\) we use two elementary facts. First no signed monomial belongs to \(J\) since \(X\) is a unit. Second \(|J|\ge e^{c_q d}\) uniformly. Indeed each simple residue of \(R\) is a residue over some prime \(p\mid q\), with the degree of a factor of \(X^d+1\bmod p\) equal to \(\operatorname{ord}_{2d}(p)\ge c_p d\) for large dyadic \(d\). The equality uses that every root has order \(2d\); the bound follows from \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\). Any nonzero ideal contains a minimal nonzero ideal, isomorphic as an \(R\)-module to one simple residue. Thus the proper contribution is at most \(e^{-c_q d}\) times the product over rows of (7), because each \(v_i\bmod q\in J\) excludes a row with only a single signed unit. That product is \(\exp(O(1+d^{1-2\delta}))=\exp(o(d))\). This establishes (3). In the same calculation for a prescribed centered unit label feature \(h\), replace the indicator by its normalized Fourier coefficient \(\widehat h\) evaluated at the random sum. Centering removes the \(J=0\) case; on any other \(J\), averaging its squared magnitude costs at most \(1/|J|\) by Parseval. The estimate then holds verbatim. Compared with Haar rather than \(G\), use the preceding \(L^2\) bound on \(G-1\) (also the two frequency classes are orthogonal). As a direct consequence, the [adaptive Gaussian-noisy summary transfer](https://github.com/mxym/math/blob/82652d91f0f5f5d3a42dd2a0b219fca4180f39f1/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-adaptive-noisy-coordinate-summaries.md) gives vanishing whole-transcript TV for the same sufficient energy regime in this correlated-noise model: apply its theorem with product Haar as the input reference and then use TV closeness of \(Q\) and Haar. That consequence still requires the prescribed observation channel and pathwise budget.

## 5. Statistical critical window

Let \(X=\log(f(Y)/g(Y))\) for a true error \(Y\sim f\) in one row. Its mean is \(C_d\), and
\[
 \operatorname{Var}_f X=2d b^2(1+o(1)).
                                                               \tag{11}
\]
Also \(|X|\) is bounded uniformly, by (8) and the estimates on \(g\). Here are details for (11) and a related shared-grid conditional mean. Let \(A_1(y)=2b\sum_j\cos(2\pi y_j)\). The independent product expansion and (8) give \(\|f-1-A_1\|_2=o(\sqrt d\,b)\): for \(f_0\) the squared mass beyond the signed one-site unit terms is \(O((db^2)^2+d b^8)\), and \(\Delta\)'s norm is smaller by \(b^\delta\). Also
\(\|f-1\|_4^2=o(\sqrt d\,b)\).
For \(f_0\) this quantity is \(O(db^2)\) since the Haar fourth moment of the sum of independent \(\log f_b^{(1)}\) terms is \(O(d^2b^4)\), and that sum is uniformly bounded. The contribution from \(\Delta\) is at most
\(\|\Delta\|_\infty\|\Delta\|_2=O(d^{3/2}b^{2+2\delta})=o(\sqrt d\,b)\).
The Taylor remainder under the uniform bounds on \(f\) now gives both
\[
 \|\log(f/g)-A_1\|_2=o(\sqrt d\,b),\qquad
 \|f\log(f/g)-(f-1)\|_2=o(\sqrt d\,b).                           \tag{12}
\]
Haar has \(\mathbb E A_1^2=2db^2\) and \(\|A_1\|_4^2=O(db^2)\). Multiplying the integral of \(A_1^2\) by \(f\) changes it by \(o(db^2)\), since \(\|f-1\|_2=o(1)\). Bounded \(f\), (12), and the order \(C_d=O(db^2)\) prove (11).

Let \(\xi=qY\bmod1\) be the invariant grid position under \(Y\sim f\), whose density relative to Haar in \(\xi\) is the function \(g\) viewed on the quotient. Conditional averaging under Haar over the \(q\)-grid coset sends \(f-1\) to \(g-1\). The second estimate in (12), divided after averaging by the bounded positive \(g\), proves
\[
 \big\|\mathbb E_f[X\mid\xi]\big\|_{L^2(\xi)}=o(\sqrt d\,b).      \tag{13}
\]
In particular a pair of true errors conditionally independent given the same \(\xi\) has covariance \(o(db^2)\) between its two log scores. Over independent rows, the sum \(Z=\sum_{i=1}^T X_i\) has a Gaussian standardized limit with mean \(TC_d\) and variance \(2t_dd(1+o(1))\), by bounded row log scores and Lindeberg. The analogous pair of sums with shared \(\xi\) in every row converges to independent standard normals under that same centering and scaling, by (13) and Cramér–Wold.

We next explain why the correlated public mixture gives (2) rather than merely the true-score CLT. Let \(L_s=dP_{Y\mid A,s}/dQ\) for a fixed label. A fraction \(1-e^{-\Omega(d)}\) of differences \(s-s'\) are units in \(R\): by the residue degree argument of §4 each nonunit lies in one of \(O_q(1)\) maximal ideals of exponentially large index. For a unit difference the relative grid shifts of the two row residuals, when averaged over \(A\) under \(Q\), are uniform on the entire grid. Conditional on the common invariant position \(\xi\), the two residuals are then independent uniform points of its grid coset. Multiplying by the product of their two likelihoods \(f/g\) has exactly unit normalizing mass conditionally on \(\xi\). It replaces both residuals by independent draws from the true law conditioned on \(\xi\), with \(\xi\)'s marginal unchanged. This proves that the weighted pair CLT above is exactly the one needed for unit differences.

For nonunit nonzero differences, let \(I=(s-s')R\ne0\). The relative shift is uniform on \(I\), and for a single row
\[
 \mathbb E_{A,Q}L_{i,s}L_{i,s'}
 \ \le\ (1+O(d b^{q^2}))
             \sum_{v\bmod q\in I^\perp} b^{2 E(v)} .
\]
Indeed \(1/g\le1+O(d b^{q^2})\) in the product integral of two positive translated densities, and orthogonality of grid phases then gives the sum. The coefficient-dot annihilator \(I^\perp\) is a proper ideal by the adjoint involution, so the sum excludes every vector with a single signed unit. Equation (7) shows that all \(T\) rows contribute only \(\exp(o(d))\) to the overlap bound, while the fraction of nonunit differences is exponentially small. This uniform comparison does not require a bivariate CLT for a nonunit difference.

Put \(M=q^d\), \(h_d\to\infty\) with \(h_d=o(\sqrt d)\), and \(U_s=L_s\mathbf1_{\{\log L_s\le\log M-h_d\}}\). Every fixed \(A\) gives \(\mathbb E_Q U_s=m=\Pr(Z\le\log M-h_d)\) by grid invariance. For the mean \(\bar U=M^{-1}\sum_s U_s\), its diagonal second moment term is at most \(e^{-h_d}m\). For distinct unit differences the weighted pair CLT gives \(m^2+o(1)\) for each averaged product irrespective of the standardized threshold, by the uniform rectangle convergence to a continuous bivariate normal. For distinct nonunit differences the total weighted contribution is \(e^{-\Omega(d)}\exp(o(d))=o(1)\). Hence \(\mathbb E_{A,Q}|\bar U-m|^2=o(1)\). The removed mass and the distance from the constant \(m\) to the reference give average upper TV \(1-m+o(1)\).

For every fixed \(A\), the union of the events \(\{\log L_s>\log M+h_d\}\) has \(Q\)-mass at most \(e^{-h_d}\), and its true mixture mass is at least \(\Pr(Z>\log M+h_d)\). This gives the matching lower bound on TV pointwise in \(A\). The two cutoffs may be merged by the one-dimensional CLT and uniform Gaussian anti-concentration in intervals of length \(o(\sqrt d)\). Thus the actual conditional TV converges in \(L^1_A\) to the Gaussian profile in (2). Equation (1) gives the stated nominal-window displacement and the distinction between first-order and second-order behavior.

Finally, to compare only the *error laws*, take disjoint adjacent coefficient pairs starting at positions \(0,3,6,\dots\) away from the wrap edge. The selected pairs are independent under the unwrapped Gaussian (cross-covariances are zero), and remain so after wrapping; they are also independent under \(f_0\). For each pair, the variable \(\cos(2\pi(Y_j-Y_{j+1}))\) has mean \(b^{1+\delta}\) under the correlated true error law and \(b^2\) under \(f_0\). The selected pairs across \(T\) rows number \(\Theta(d^3)\), and their bounded observations have mean-estimate standard deviation \(O(d^{-3/2})\). When \(\delta<1/2\) the mean gap dominates that scale, and Chebyshev separates the two error laws in TV. This is a comparison of standalone error distributions, not a test given noisy responses with an unknown label.

## 6. Earlier work and scope

[Lyubashevsky–Peikert–Regev, On Ideal Lattices and Learning with Errors over Rings](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf), §1.2, uses Gaussian ellipses in the canonical real space; its reductions have different hypotheses. The present \(I+\rho(U+U^\top)\) covariance is diagonal in the antiperiodic Fourier eigenspaces but is not iid in the coefficient basis. This fixed theoretical covariance, fixed odd modulus, and broad scaling are not statements about the parameters or hardness conclusions of those reductions.

The earlier [independent-coordinate spectrum and TV calculation](https://github.com/mxym/math/blob/1aaf3b754c946fbefcfadcdee20fd3ae10648a1b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-coordinate-degree-and-tv.md) gives stronger absolute profile control in its product model. Here the nonproduct support-component count and the shared-grid paired likelihood normalization are needed instead. [The earlier abstract antiperiodic theta cutoff](https://github.com/mxym/math/blob/d7b4217a47b9dace0513047b2c3e0c5bf9f64d8d/research/euclidean-tensor-geometry/theoretical-cryptography/dyadic-dipole-cutoff.md) treats a different kernel and theta scaling; it does not give the response-law divergence correction, shifted statistical window, or survival of the coordinate-degree obstruction shown here. We do not claim the same correction for arbitrary covariance or for \(\rho\) depending on \(d\), nor an efficient decoder or a general computational lower bound.
