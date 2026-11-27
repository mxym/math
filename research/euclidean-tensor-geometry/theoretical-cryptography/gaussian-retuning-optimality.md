# Global optimality of the fourth-order Gaussian rounding threshold

The [previous rounding calculation](gaussian-rounding-critical-scales.md) fixed the Gaussian source covariance at σ²A or σ²A−I/12. Does another choice of mean and covariance remove the remaining fourth-order statistical discrepancy? For independent fixed-dimensional blocks the answer is **no, even with arbitrary independent retuning allowed for every block**. On the integer lattice the variance-compensated Gaussian already gives the best limiting product total variation. On a coefficient quotient of comparable period the optimal constant is a projection of the earlier Fourier-periodized score, but still strictly positive.

This is a statistical comparison of standalone noise laws. It does not concern the full observations in Ring-LWE, a deployed design, quantization of a secret-dependent signal, or alternatives that correlate different blocks or are not Gaussian. For earlier rounded-versus-discrete comparisons see [Hülsing, Lange and Smeets, Rounded Gaussians](https://iacr.org/archive/pkc2018/10770212/10770212.pdf), and [TRaccoon, Appendix E](https://eprint.iacr.org/2024/184), which already notes the 1/12 variance correction and compares fixed-width laws by Rényi divergence. The issue here is the global infimum and its exact total-variation transition, not the correction itself.

## The optimization and the answer

Fix a block dimension b and a positive definite symmetric b×b matrix A, and let σ→∞, u=1/σ. On block i the reference Q_i is the discrete Gaussian on Z^b with weight proportional to the density of N(μ_i,σ²A). Centers μ_i may vary arbitrarily. An admissible P_i is obtained by coordinatewise nearest-integer rounding of any real Gaussian with any mean ν_i and any positive definite covariance Σ_i. No closeness, boundedness or convergence of those parameters is imposed in the infimum. Let all blocks be independent in both products. There are two versions of the experiment: integer outputs as above, or reduce *both* outputs coordinatewise modulo an integer Q with Q/σ→α∈(0,∞).

Write g for the density of Z∼N(0,A). Define the fourth-order score H and Gaussian parameter tangent T by
```
H(z) = −Σ_j ∂_j⁴ g(z) / (2880 g(z)),
T_(a,S)(z) = aᵀA⁻¹z + (zᵀA⁻¹SA⁻¹z − tr(A⁻¹S))/2,
```
where a∈R^b and S is any real symmetric b×b matrix. Define the linear operator Π to be the identity (integer model), or conditional expectation given Z modulo α (quotient model). For both cases put
```
v_* = min_(a,S) E[(Π[H+T_(a,S)])²].
```
In the integer model
```
v_* = E[H²] = 4! Σ_ij ((A⁻¹)_ij)^4/2880²,
```
and the unique minimizer is (0,0). In the quotient model there is also a unique minimizer; the projected mean component is zero, but the covariance component need not be. In both cases v_*>0.

Uniformly in the reference centers, the infimum squared Hellinger distance between one such P and Q, with convention h²=1−∫√(dP dQ), is (v_*/8+o(1))σ⁻⁸; the infimum χ² is (v_*+o(1))σ⁻⁸. If N/σ⁸→τ∈[0,∞], the global infimum over all N allowed independently retuned Gaussian sources satisfies
```
inf TV(⊗ P_i, ⊗ Q_i) → 2Φ(√(v_* τ)/2)−1 ,
```
with value one at τ=∞. In particular no retuning increases the order of the threshold past σ⁸. At finite positive τ the limit is achieved by using, with (a_*,S_*) any chosen minimizing pair above,
```
ν_i = μ_i + σ⁻³ a_*,    Σ_i = σ² A − I/12 + σ⁻² S_* .
```
These parameters stay positive definite for σ large. The optimization over different block retunings is not a claim about a single giant Gaussian with arbitrary cross-block covariance. The quotient theorem assumes a finite positive limiting scaled period; it does not claim a global retuning optimum when Q/σ→0 or ∞.

## Local expansion and variance

Rescale the centered candidate mean and covariance as a=(ν−μ)/σ, B=Σ/σ². Use `η=(a,S)` to denote deviations from the compensated source, so B=A−u²I/12+S. Near η=0 the likelihood ratio difference under the discrete reference satisfies
```
dP/dQ − 1 = u⁴ H(z) + T_η(z) + R,
‖R‖_p = O(u⁶+u²‖η‖+‖η‖²),    p=2,3,4,     z=(k−μ)/σ.
```
The compensated term and the Gaussian envelope bounds come from the [earlier expansion](gaussian-rounding-critical-scales.md). The remaining estimate follows by differentiating the exact cell integral in (a,S). At u=0, η=0 its linear derivative is exactly T_η, by differentiating the normal density. Its difference from the corresponding derivative at u>0, η=0 is O(u²) in each stated norm: the cell integral is even in u and its covariance baseline differs by O(u²). Uniform second η derivatives are bounded in these norms. To justify the differentiations and norms, in a fixed small neighborhood of (u,η)=0 the differentiated likelihood ratios are bounded by a polynomial in ‖z‖ times exp(C(|u|+‖η‖)‖z‖+C(u²+‖η‖)‖z‖²+C); the neighborhood can be small enough that the p-th power times g is bounded by a fixed integrable Gaussian times a polynomial. The uniform shifted Gaussian lattice bounds and exponentially accurate normalizer used earlier then apply. All errors are uniform in μ.

In the quotient model the likelihood and each term are replaced by their conditional expectations under Q given the residue. This contracts L^p. The conditional-score moment matrix tends uniformly in μ to the corresponding continuous periodized moment matrix with period α, by the Riemann sum argument in the preceding note. In the integer model the moment matrix tends uniformly to the Gaussian moment matrix. In either model along any u→0, η→0, with `e²=u⁸+‖η‖²`,
```
E_Q[(dP/dQ−1)²] = E[(Π[u⁴H+T_η])²] + o(e²),
E_Q[|dP/dQ−1|^j] = O(e^j)  for j=3,4.
```
For the squared-distance formula, a finite basis of score polynomials suffices to compare their entire Gram matrix, so convergence is uniform as η/u⁴ varies. The remainder is o(e) in norm. As before the likelihood difference is centered exactly, and replacing the expectation defining χ² by the Hellinger expression gives factor 1/8 plus o(e²), using the third moment.

In the integer model the score H is fourth Hermite chaos; T consists of linear and centered quadratic chaos. Orthogonality follows, for example, by Gaussian integration by parts against a polynomial of smaller degree. The exact tangent squared norm is
```
aᵀA⁻¹a + (1/2) tr[(A⁻¹ S)²],
```
which is positive definite in (a,S). In the quotient model, multiplication by the everywhere-positive wrapped density turns the projected scores into periodized density derivatives. Relative to the nonzero Gaussian Fourier coefficient at frequency ω=2πk/α, their Fourier multipliers (with the negative sign convention for the transform) are
```
ΠH: −Σ_j ω_j⁴/2880,   ΠT_(a,S): −i ωᵀa − ωᵀSω/2 .
```
The tangent map on this integer-frequency grid is injective: test e_j and e_j+e_l and compare real/imaginary parts. Moreover no tangent cancels the quartic multiplier since along any coordinate axis it grows as the fourth rather than the second power. Thus the span is finite dimensional and closed, the orthogonal residual has squared norm v_*>0, and the unique least-squares minimizer exists. Periodized mean scores are odd and the density, the fourth score, and covariance scores are even on the torus, so a_*=0. These arguments show that the combined fourth and tangent Gram form is positive definite in the scalar coefficient of H and coordinates of η, in both experiments. In particular the above expansions are nondegenerate.

The wrapped correction can strictly improve upon ordinary compensation. For example take b=1,A=1 and a small but fixed α. With ω=2π/α and c=exp(−ω²/2), in normalized angle the wrapped density is 1+2c cos(y)+O(c⁴), its second derivative numerator starts at −2ω²c cos(y) and the fourth at 2ω⁴c cos(y), with errors O(ω²c⁴), O(ω⁴c⁴), respectively. The fourth and covariance scores therefore have inner product `ω⁶c²/2880 + O(ω⁶c³)`: multiply their leading numerators, divide by the wrapped density, and average cos²(y)=1/2. It is nonzero for sufficiently small fixed α. The strict gain is on the constant, not the exponent.

## Global localization: why unrestricted parameters do not improve the result

Let P_c be the law from the compensated source (a=0,B=A−u²I/12). Write h=h(P,Q) for the single-block Hellinger distance. Whenever h→0, necessarily a→0 and B→A; in the quotient experiment, a is read modulo α_σ=Q/σ and a representative near zero is used. Here is a direct justification, also permitting unbounded or degenerating source covariances in the initial infimum.

After scaling, the rounding error is pointwise at most √b u/2. For any fixed frequency t, the characteristic function of the rounded sample differs from that of N(a,B) by at most ‖t‖√b u/2. In the integer model the centered scaled reference tends weakly to N(0,A) uniformly in μ (shifted Riemann sums). When h→0, total variation tends to zero, so the Gaussian characteristic functions converge pointwise to that same normal. For t=e_j,e_j+e_l, their magnitudes imply B→A. Bounded covariances and tightness of the Gaussians force the means to stay bounded, and convergence of all phases gives a→0. In the quotient model use t=2πk/α_σ and the reference wrapped Gaussian limit. The same finite set of k gives B→A from magnitudes, and the phases for k=e_j give a modulo α_σ converging to zero. Shifting the source mean by an integer multiple of Q does not change its rounded law reduced modulo Q.

There is also a quantitative local version, uniform in μ and u small:
```
‖η‖ ≤ C (h+u⁴)   whenever h is sufficiently small.
```
Use the finite vector of real and imaginary characteristic values at those frequencies. At the Gaussian baseline its derivative in (a,S) has full column rank: the phase derivatives detect mean coordinates and the magnitude derivatives recover all entries of S. The derivative for the rounded values differs from the Gaussian derivative by O(u) locally uniformly, including in μ. Indeed differentiate a bounded characteristic test of the rounded value by multiplying with the Gaussian score and integrating against the unrounded Gaussian density. The bounded difference between the rounded and unrounded characteristic test is O(u) pointwise, and the Gaussian scores have uniformly bounded L¹ norms in a fixed neighborhood. Thus throughout a small neighborhood the derivative of the vector differs by arbitrarily little from a fixed injective map (use the limiting frequencies in the quotient model), giving a lower Lipschitz bound on differences by integration along line segments. Apply it between P and P_c. The characteristic vector difference is O(TV(P,Q)+TV(P_c,Q))=O(h+u⁴), as before. Qualitative localization by a subsequence contradiction guarantees entrance into that neighborhood uniformly whenever h is small and u is small.

This suffices to prove the asserted global single-block optima. The displayed admissible retuning attains the local minimal expansion. Conversely, any sequence competitive with this for Hellinger has h=O(u⁴) and hence η=O(u⁴), uniformly in the center. Its leading squared score is at least v_*u⁸. The same localization works if competing for χ², since h²≤χ²/2; the local likelihood expansion then gives the lower bound for χ² as well. An infimum may always be handled using models approaching it; compactness beyond the quantified localization is not needed.

## Products with arbitrary heterogeneous retuning

The optimizing common correction attains the claimed upper bound by the likelihood central-limit proof from the earlier note, with the projected residual score if wrapped. The endpoint τ=0 is immediate. For τ=∞ the positive global single-block lower bound makes the product affinity tend to zero for *every* candidate family, so TV tends to one uniformly.

For 0<τ<∞ consider any sequence whose product TV stays bounded away from one; otherwise there is no lower bound left to prove. The product affinity is bounded below because h²≤TV, so the sum of squared block Hellinger distances is bounded. Choose L→∞ sufficiently slowly so Lu⁴→0. Discard blocks with h_i>Lu⁴. There are O(L⁻²u⁻⁸)=o(N) of them, and projecting away blocks cannot increase TV. For the retained blocks the quantitative localization gives max‖η_i‖=O(Lu⁴)=o(1) and
```
Σ_i (u⁸+‖η_i‖²) = O(Nu⁸ + Σ_i h_i²) = O(1).
```
Thus the uniform local error, summed over the retained blocks, is o(1). Each squared projected leading score is at least u⁸ v_* by homogeneity and the definition of v_*, so the variance sum has liminf at least τv_*. The variance sum is bounded, and along any subsequence on which it tends to V it is positive. The sum of third and fourth likelihood-difference moments tends to zero, by the preceding bounds and max(u⁴+‖η_i‖)=o(1). Consequently the triangular-array log-likelihood under the reference converges to N(−V/2,V), exactly as in the earlier note (Lyapunov, squared sum concentration, and the cubic log remainder). Convergence of expectations of the bounded continuous function (1−exp(x))_+ along this distributional convergence gives TV limit 2Φ(√V/2)−1 for the retained product, at least the claimed lower bound. The argument is uniform in all block centers and candidates; passing to nearly minimizing candidate sequences proves the global statement. This is a statement about the product-TV infimum, not a claim that unwrapped L² orthogonality alone optimizes the exact finite single-block TV.

[The checker](verify-gaussian-retuning-optimality.js) verifies exact Hermite inner products and the unwrapped scalar residual constant by rational arithmetic, and illustrates the wrapped projection using fixed toy periods and deterministic quadrature.
