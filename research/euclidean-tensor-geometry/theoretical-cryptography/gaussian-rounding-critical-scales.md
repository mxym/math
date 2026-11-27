# Nearest-rounded versus discrete Gaussian: two sharp statistical scales

Let a continuous normal of large coefficient width σ be rounded to the nearest integer in each coefficient. This law is not the same as the discrete Gaussian obtained by evaluating the normal density at lattice points and normalizing. This note gives exact total-variation transitions for repeated fixed-dimensional blocks, both on the integer lattice and on coefficient quotients of period comparable to σ. It is a comparison of two noise laws, not a claim about a cryptosystem or an efficient way to distinguish its outputs.

The variance compensation by 1/12 used below is not new. [TRaccoon, Appendix E](https://eprint.iacr.org/2024/184) explicitly notes this compensation and gives Rényi estimates for the same-width comparison, for simplicity omitting the compensation from those estimates. [Gama, Narayanan, LiuLin and Yue](https://eprint.iacr.org/2023/1288) instead construct a different continuous source whose rounding gives an exact discrete Gaussian. [Peikert's randomized lattice rounding](https://eprint.iacr.org/2010/088) is a different map, not deterministic nearest rounding. This note does not assert priority for these distinctions; the results here are the second- and fourth-order likelihood profiles, their exact product-TV thresholds, and what reduction modulo Q does to the constants.

## Distributions and main theorem

Fix a block dimension b and a real symmetric positive definite b×b matrix A. Put σ→∞, choose arbitrary centers μ∈R^b, and let q_{σ,μ} be the discrete law on Z^b with mass proportional to the density of N(μ,σ²A) at each integer point. Let p_{σ,μ} be the result of coordinatewise nearest-integer rounding of either N(μ,σ²A), the uncompensated case, or N(μ,σ²A−I/12), the compensated case. The latter is positive definite for all sufficiently large σ. Both q and p are strictly positive.

Write g_A for the density of N(0,A), Δ for the usual Euclidean Laplacian, and define the order r, score H and its variance v as follows:
```
                        r          H(z)                          v
uncompensated           2          (Δg_A)/(24g_A)                2 tr(A⁻²)/24²
compensated             4          −Σ_i ∂_i⁴g_A/(2880g_A)        4! Σ_ij ((A⁻¹)_ij)^4/2880²
```
For either case and for every even integer p-moment order up to four (also for the L³ norm),
```
p_{σ,μ}(k)/q_{σ,μ}(k) − 1 = σ^(−r) H((k−μ)/σ) + O_{L^p(q_{σ,μ})}(σ^(−r−2)),
```
uniformly in μ. In particular, each block has χ²(p,q)∼vσ^(−2r), squared Hellinger distance h²=1−Σ_k√(p(k)q(k))∼vσ^(−2r)/8, and single-block total variation ∼σ^(−r) E|H(Z)|/2 for Z∼N(0,A).

Take N independent such blocks of width σ, using the same A but arbitrary centers that may differ across blocks and arbitrarily with σ and N. If N/σ^(2r)→τ∈[0,∞], then
```
TV(⊗ p_{σ,μ_i}, ⊗ q_{σ,μ_i}) → 2Φ(√(vτ)/2)−1,
```
where Φ is the standard normal distribution function and the value at τ=∞ is one. For A=I and b=1, v is 1/288 uncompensated and 1/345600 compensated. Thus d independent coefficients have sharp count/width^4 or count/width^8 scales, respectively, not a naive union-bound scale.

## Likelihood expansion

Use u=σ⁻¹ and x=(k−μ)/σ. Let K=[−1/2,1/2]^b, and δ=0 or 1/12. The exact unnormalized ratio for a cell at k is
```
R(u,x) = ∫_K g_{A−δu²I}(x+ut)/g_A(x) dt.
```
The ratio p/q is R multiplied by the normalization sum σ^(−b) Σ_k g_A((k−μ)/σ), which is 1+O_A(exp(−c_A σ²)) uniformly in μ by Gaussian Poisson summation. In particular the offset of the center relative to the integer grid does not appear in the leading score. The normalizer multiplying R is positive and all formulas are for probabilities rather than an approximation to their normalization.

Taylor expansion of the cell averaging operator through order four gives
```
1 + u²Δ/24 + u⁴[Σ_i ∂_i⁴/1920 + Σ_{i<j}∂_i²∂_j²/576].
```
The covariance direction satisfies ∂_a g_{A+aI}=Δg_{A+aI}/2 (differentiate the Gaussian or its Fourier transform). Thus covariance change contributes the operator expansion 1−δu²Δ/2+δ²u⁴Δ²/8, through order four, when this differential operator is applied to g_A. With δ=1/12 the second-order term and all mixed fourth-order derivatives cancel; the pure fourth-order term is −u⁴ Σ_i∂_i⁴/2880. With δ=0 the leading term is u²Δ/24.

Here truncation is in L^p, not a uniform relative approximation over all lattice points. For completeness, for fixed A,b and sufficiently small |u| the derivatives of R(up to order six) are bounded in magnitude by
```
C(1+‖x‖^C) exp(C|u|‖x‖+Cu²‖x‖²+C).
```
Indeed each Gaussian ratio has the exponential of a quadratic whose quadratic coefficient is O_A(u²), linear coefficient O_A(|u|), and constant bounded uniformly over compact K; differentiation multiplies by polynomials in x with bounded coefficients for u in a sufficiently small compact interval. Integration over K preserves the bound. Choose the interval small enough that the p-th power envelope times g_A is bounded by a fixed Gaussian times a polynomial, for p≤4. Uniform shifted lattice Gaussian moment bounds follow by a cell comparison to the corresponding integral (or bounded Riemann sums with uniformly integrable Gaussian tails). The symmetry t↦−t makes R even in u. Taylor through degree three or five with this envelope gives O_{L^p}(u⁴) or O_{L^p}(u⁶), respectively. The normalizer does not change these error orders.

Every score has mean zero under g_A by integrating Gaussian derivatives. For W=A⁻¹Z the covariance is A⁻¹, and the derivative ratios of orders two and four are Wick powers of its coordinates: e.g. ∂_i⁴ g_A/g_A=W_i⁴−6(A⁻¹)_ii W_i²+3(A⁻¹)_ii². The cross-moment of equal-order Wick powers in coordinates i,j is r![(A⁻¹)_ij]^r, as follows by comparing coefficients in the centered exponential moment generating functions. Squaring the scores and summing gives v. Shifted lattice Riemann sums of these polynomial moments converge uniformly in μ (periodicity in μ modulo Z^b allows the shift to range over one compact cell). This establishes the χ² and TV equivalents. The Hellinger equivalent follows from the identity
```
2h²=E_q[(p/q−1)²/(√(p/q)+1)²].
```
On |p/q−1|≤1/2 the denominator inverse differs from 1/4 by O(|p/q−1|); the remaining expectation is O(E_q|p/q−1|³).

## Product transition

Under the reference product law, let X_i=p_{σ,μ_i}(K_i)/q_{σ,μ_i}(K_i)−1. They are independent and centered, with variance ∼vσ^(−2r) uniformly, and E|X_i|^j=O(σ^(−rj)) for j=3,4. When 0<τ<∞, Lyapunov gives Σ X_i⇒N(0,vτ), and Σ X_i²→vτ in probability by the fourth-moment bound. The maximum |X_i| exceeds 1/2 with probability o(1) by the third-moment union bound; on its complement the logarithm remainder has magnitude O(Σ|X_i|³)=o_p(1). Hence the log-likelihood under the reference tends to N(−vτ/2,vτ). Total variation is the expectation of (1−exp(log-likelihood))_+ under that reference. This is bounded continuous in the log-likelihood, and its limiting normal integral is 2Φ(√(vτ)/2)−1. For τ=0 the product affinity tends to one; for τ=∞ it tends to zero. In terms of the above h², h²≤TV≤√(2h²), which also proves the respective endpoint limits.

## Modulo Q: the leading information is attenuated, not erased automatically

Now reduce every integer coordinate modulo the same positive integer Q, allowed to depend on σ. Let α=lim Q/σ. For α∈(0,∞) the entire theorem for block products remains true with v replaced by
```
v_A(α) = ∫_[0,α)^b [Σ_{m∈Z^b} g_A(x+αm) H(x+αm)]²
                             / [Σ_{m∈Z^b} g_A(x+αm)] dx.
```
In both cases 0<v_A(α)<v. If α=∞ then the original constant v is recovered and no additional factor of √log σ is needed. The regime Q/σ→0 is not included in this sharp statement.

To see this, for each residue r' the new likelihood difference is the conditional expectation of the original one given K modulo Q, under q. Conditional expectation contracts L^p, so all error bounds remain valid after replacing the score by its conditional expectation. It has mean tending to zero, its centered likelihood difference remains exactly centered, and the product proof applies as soon as the second moment of this conditional score is identified. For finite positive α, in scaled centered coordinates and with α_σ=Q/σ this conditional score is exactly
```
[Σ_m g_A(x+α_σ m)H(x+α_σm)]/[Σ_m g_A(x+α_σm)].
```
The sums converge uniformly with derivatives on bounded fundamental cells for α_σ in a compact subinterval of (0,∞), and the denominator is uniformly bounded below by a positive constant (use a nearest representative in the compact fundamental cell). The uniform Riemann sums of the squared score against periodized g_A therefore converge to the displayed integral; the residue grid includes a shift by −μ/σ but has mesh σ⁻¹ and the integrand is periodic. The integral is the second moment of E[H(Z) | Z modulo α]. Strict reduction from v follows since a nonconstant polynomial cannot be periodic, whereas zero conditional variance would imply almost-everywhere periodicity under an everywhere-positive Gaussian density. Strict positivity follows because periodized g_A H is a constant times Δ or Σ_i∂_i⁴ of the periodized Gaussian: the Fourier coefficient at frequency e_1/α is the corresponding nonzero derivative multiplier times a positive Gaussian Fourier coefficient.

For α=∞ use the coordinatewise centered representative x' of x modulo α_σ. It is measurable in the residue and agrees with x whenever all coordinates lie within (−α_σ/2,α_σ/2]. Else |x'_i|≤|x_i| for each i. The L² distance between H(x) and H(x') tends to zero uniformly in the shifts by polynomial growth and Gaussian tails. Conditional expectation is the L² projection, so its distance from H(x) is no larger. This proves convergence of its second moment to v in this case also.

## Power-of-two rings

In S=Z[Y]/(Y^d+1), d a power of two, the full canonical embedding of the coefficient basis has mutually orthogonal columns with squared norm d, by the sum over odd powers of a primitive (2d)-th root. Thus for spherical N(0,σ²) in coefficient coordinates, the scalar product result applies immediately (a change of common scale converts to canonical widths). For the codifferent lattice S^∨=(1/d)S use its scaled coefficient basis and measure widths in units of its own lattice spacing. Reduction modulo Q is precisely coefficientwise reduction on either lattice.

The block setting includes genuine canonical ellipses. For fixed b a power of two dividing d, write h=d/b and J for the d-dimensional negacyclic signed shift. Any positive, real, self-adjoint covariance polynomial a(J^h) has independent identical blocks indexed by coefficient residue modulo h. In each block it is the same A=a(J_b) with J_b the b-dimensional negacyclic shift; the canonical eigenvalues are positive and conjugate-equal. A concrete choice is b=4 and a(J_b)=I+(J_b−J_b³)/3. Here A⁻¹=(9/7)I−(3/7)(J_b−J_b³), so tr(A⁻²)=396/49 and Σ_ij((A⁻¹)_ij)^4=26892/2401. These examples include nonzero coefficient correlations. The argument does not treat a dense growing-block covariance shape or claims about discretizing a secret-dependent signal. Compare [Lyubashevsky–Peikert–Regev's canonical noise](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) and the distinct worst-case reductions of [Peikert–Regev–Stephens-Davidowitz](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf); no consequence for those reductions' parameters is asserted here.

[The small checker](verify-gaussian-rounding-threshold.js) checks the differential coefficients and variance constants by exact rational arithmetic and illustrates the scalar χ² asymptotics with deterministic Gauss–Legendre quadrature. The analytical proof, not the numerical illustration, establishes the limits.
