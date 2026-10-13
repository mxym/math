# Full Wishart determinant-product stage

14 October 2026, Asia/Shanghai. Internal written-breadth agent.
Status: bounded discovery and analytic exploration; no solution or counterexample to the full conjecture obtained.

## Original object and whole target

The target is Conjecture 1.1 of [Genest–Ouimet–Richards, arXiv:2311.00202v3](https://arxiv.org/html/2311.00202v3):
\(W\sim W_p(\nu,\Sigma)\), every real \(\nu>p-1\), every real positive definite scale matrix, arbitrary disjoint diagonal block sizes summing to \(p\), and every \(a_i\geq0\). It asks for
\[
 \mathbb E\prod_i\det(W_{ii})^{a_i}
 \ \geq\ \prod_i\mathbb E\det(W_{ii})^{a_i}.             \tag{W}
\]
A single actual SPD scale matrix and a legally admissible noninteger degree with strict reverse inequality would disprove this entire assertion. Conversely, neither a finite search nor a theorem for a chosen rank, block configuration, integer degree, or exponent family solves (W).

The two-block problem is already solved in [Genest–Ouimet–Richards, arXiv:2409.14512](https://arxiv.org/abs/2409.14512), published in Proceedings of the AMS in 2025. The 2026 [Gaunt–Ouimet recursion, arXiv:2607.03984v1](https://arxiv.org/html/2607.03984v1) computes all nonnegative **integer** determinant-power moments for arbitrary blocks and real \(\nu>p-1\). Its exact evaluation algorithm is not a proof of (W), and its closing remark explains why real-power differentiation no longer gives a finite polynomial recursion.

The actual Conjecture 1 in [Genest–Ouimet, arXiv:2206.01976v2](https://arxiv.org/html/2206.01976v2) asks instead for arbitrary **grouped** trace moments. Its literal degree range includes \(\nu=1\); the grouped one-degree Gaussian failure was already explicitly given in Section 1 of [Edelmann–Richards–Royen, arXiv:2204.06220v2](https://arxiv.org/html/2204.06220v2). No new major refutation is claimed by recognizing that failure.

## Exact singleton coefficient route

For \(Y_i=W_{ii}\) when \(W\sim W_p(2\beta,R/2)\), \(\beta>(p-1)/2\),
\[
 F(t)=\mathbb E e^{\sum_i t_iY_i}
      =\det(I-R\operatorname{diag}t)^{-\beta}
      =\sum_{k\in\mathbb N_0^p} f_k t^k
\]
near zero. Put \(d_S=(-1)^{|S|}\det R[S]\), including \(d_\varnothing=1\), and \(1_S\) for the indicator vector. Then
\[
 k_i f_k
 =-\sum_{\varnothing\ne S\subseteq\operatorname{supp}k}
   d_S\left[k_i+(\beta-1)1_{\{i\in S\}}\right]f_{k-1_S},
 \quad k_i>0,\quad f_0=1.                              \tag{C}
\]
Indeed multiply \(\partial_iF=-\beta F(\partial_iD)/D\), \(D=\sum_Sd_St^{1_S}\), by \(D\) and take coefficient \(t^{k-e_i}\). Equation (C) is a finite exact moment formula:
\(\mathbb E\prod_iY_i^{k_i}=f_k\prod_i k_i!\).
The diagonal-independent comparison coefficient is
\(\prod_i(\beta)_{k_i}R_{ii}^{k_i}/k_i!\).

The signs in (C) alternate with \(|S|\); PSD principal-minor nonnegativity does not turn this into a termwise positivity proof of the excess over independence. One cannot interpolate a sign inequality at half-integer shapes to all real shapes merely because this moment is polynomial in the shape.

The file exploration/wishart_singleton_probe.py differentiates (C) with respect to the principal determinant coefficients and chains the exact cofactor derivative through normalized Gram rows. Every floating scale matrix is actually
\(R=(1-\varepsilon)VV^{\mathsf T}+\varepsilon I\), \(\varepsilon=10^{-6}\), with unit rows, so it is SPD. Six explicitly bounded exponent/degree configurations in dimensions 4–6, five starts each, produced no ratio below one beyond floating roundoff. See wishart-singleton-discovery-20261014.json. Identity-covariance controls and finite-difference gradient controls passed. These 30 observations are discovery only.

### Known negative control, with the right statement

Take
\[
 R=\begin{pmatrix}1&1/5&1/5\\1/5&1&-9/10\\1/5&-9/10&1\end{pmatrix}.
\]
Its leading principal minors are \(1,24/25,19/500\), so it is strictly positive definite. At \(\beta=1/2\), \(Y_i=G_i^2/2\) for \(G\sim N(0,R)\). The actual moments are
\[
 \mathbb EY_1Y_2Y_3=623/2000,\qquad
 \mathbb EY_1\,\mathbb EY_2Y_3=131/400,
\]
and their difference is \(-2/125\). This checks the grouped-failure control in the discovery implementation. It does not refute (W), whose whole-product right side here would be \((1/2)^3\), and whose nonsingular-Wishart degree condition in dimension three would require \(\nu>2\).

## Actual determinant-block moment route

For positive integer \(\nu\), write
\(W_{ij}=\sum_{\ell=1}^{\nu}G_{\ell i}G_{\ell j}\) with independent Gaussian rows of covariance \(R\). For a product of \(N\) matrix entries, attach two Gaussian slots to each entry and enumerate perfect matchings. A matching contributes the product of its covariance edges times \(\nu^{c}\), where \(c\) is the number of connected components formed by the matching together with the original entry-pair bonds. This is the number of independent sample labels left by the Wick constraints.

For fixed \(R\), the actual Wishart entry moment is polynomial in \(\nu\), as follows directly by differentiating its determinant-power MGF. Agreement at every positive integer therefore identifies the same polynomial at all admissible real degrees. Expanding each chosen block determinant by its signed permutations gives an exact finite joint-moment polynomial, not a sampled Gaussian approximation.

The second discovery implementation, exploration/wishart_determinant_probe.py, uses this formula with each block whitened to identity. The three configurations are (2,2,2), (3,2,1), and (2,2,1), each at determinant powers one and two noninteger admissible degrees. Their exact covariance polynomials have respectively 519, 342, and 97 nonzero integer-coefficient terms. Their full coefficients and covariance variables are preserved in wishart-block-determinant-discovery-20261014.json. Each floating scale is a Gram matrix of orthonormal rows within each block, mixed with \(\varepsilon I\), hence is SPD and has identity diagonal blocks. All 36 bounded starts produced no violation. Identity-scale controls matched the exact marginal product
\(\prod_i\prod_{j=0}^{p_i-1}(\nu-j)\).

No positive theorem about these three configurations is inferred. The multiblock signed covariance monomials do not provide a nonnegative general decomposition. Repeating larger numerical campaigns does not address the all-real-powers barrier and has not been authorized as a replacement for the proof.

## Complete corollary saved separately

The latest scalar Gaussian theorem of Ouimet–Greaves, arXiv:2609.20234v1, allows a complete all-dimension Euclidean block-norm/PSD quadratic-form inequality with all equality cases by averaging one-dimensional projections over spheres. The proof is saved as GAUSSIAN_QUADRATIC_FORM_COROLLARY.md, with complex proper/improper boundary conditions made explicit.

Its Gaussian input is attributed and pre-existing. It covers arbitrary positive real powers of arbitrary PSD quadratic forms, not determinant forms. Its integer-degree Wishart trace consequence does not reach arbitrary real degrees or (W). It is not counted as this project solving the original Gaussian conjecture or as a new major problem.

## Remaining analytic obstruction

1. A Wishart Gaussian sample representation exists at integer degrees but cannot be extrapolated to all real \(\nu>p-1\). General full-matrix Wishart laws are not available at every positive residual shape, so subtracting the integer part of \(\nu\) does not supply a permissible independent Wishart remainder.
2. Positive determinants are nonlinear volumes. The spherical linear-projection argument used for quadratic forms does not make a determinant projection Gaussian.
3. The exact integer-exponent Stein chain introduces full entry polynomials with signed coefficients. For arbitrary real exponents its inverse-block factors are nonpolynomial and its chain does not terminate. No sign-preserving closure has been proved.
4. The known two-block special-function inequality is not a license to multiply or iterate it over a correlated third block. That would require a stronger conditional or grouped inequality not supplied by the published theorem.

The stage remains exploration until one complete general proof or an independently exact-certified admissible counterexample is obtained. Time spent on requested APPT manuscript service reviews is excluded from the 45–90 minute no-breakthrough switching threshold. No new Lean package, root edit, push, publication, or submission occurred.

## Analytic checks after the finite discovery campaign

For a fixed block partition, take \(R(t)=I+tH\), where \(H\) is symmetric and has zero diagonal blocks, and \(t\) is sufficiently small that the scale is positive definite. Let
\[
 J(t)=\frac{\mathbb E_{R(t)}\prod_i\det(W_{ii})^{a_i}}
                 {\prod_i\mathbb E_{I}\det(W_{ii})^{a_i}},
 \qquad W\sim W_p(\nu,R(t)),\quad \nu>p-1,\quad a_i>0.
\]
The density integral is analytic in \(t\) near zero: for scales in a compact SPD neighborhood, each derivative is bounded by a polynomial in the matrix norm times a fixed integrable Wishart exponential density. Block sign flips leave every diagonal determinant unchanged. Consequently a second-order cross-covariance term can involve only one unordered pair of blocks; terms joining two different pairs vanish by the sign parity at a block of odd incidence.

Setting all other cross blocks to zero reduces each surviving second-order term to the already proved two-block formula. Its canonical correlation matrix is \(tH_{ij}\) up to an irrelevant sign. Expanding Theorem3.1's matrix hypergeometric function at zero gives
\[
 J(t)=1+\frac{2t^2}{\nu}\sum_{i<j}a_i a_j\|H_{ij}\|_{\mathrm F}^2
          +O(t^3).                                      \tag{L}
\]
Thus the whole conjecture has a strict local minimum at independence along every nonzero fixed cross-covariance direction with active positive exponents. This is a route diagnostic, not a complete global theorem or a new major-problem count. It explains why an infinitesimal perturbation search at independence will not generate a counterexample.

Termwise positivity of the higher Taylor series is already false in the solved scalar two-block case. For powers \(a_1=1/2,a_2=3/2\) and correlation \(t\),
\[
 {}_2F_1(-1/2,-3/2;\beta;t^2)
 =1+\frac{3}{4\beta}t^2-\frac{3}{32\beta(\beta+1)}t^4+O(t^6).
\]
The negative fourth-order coefficient is exact although the full two-block inequality holds. Therefore proving only that low-order covariance coefficients are nonnegative cannot replace the required general resummation or sign argument.

Conditioning cannot supply the missing theorem by invoking the centered Gaussian input at every conditional step. For independent standard \(Z,U\), set
\[
 X=1+Z,\quad Y=1-\tfrac9{10}Z+\sqrt{19/100}\,U .
\]
These form a noncentral Gaussian pair with SPD covariance. Their square-product deficit is
\[
 \mathbb E X^2Y^2-\mathbb E X^2\,\mathbb E Y^2
 =2(9/10)^2-4(9/10)=-99/50<0.
\]
Hence the centered theorem fails after arbitrary noncentral conditioning. This is an exact obstruction to that proof step, not a counterexample to the actual central Wishart conjecture.
