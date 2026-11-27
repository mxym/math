# Exact wrapped Gaussian profiles on prime cyclotomic lattices

For the root lattice A_(p−1) and its dual, the two Gaussian smoothing parameters and the actual total-variation mixing curves can be evaluated as the prime p grows. Both wrapped laws approach uniform at widths of the same leading size, but their limiting profiles differ: the root torus has a Gaussian likelihood limit, and the dual torus has a Bessel-function limit because it forgets one common circle phase. These are different prime-conductor lattices from the [dyadic ramified family](ramified-ideal-smoothing.md).

This is a geometric, standalone noise comparison. No public Ring-LWE samples, secrets, schemes or actual parameter sets are involved; a lower bound for a standalone wrapped law is not a lower bound for its observability in a full hidden-signal experiment. For the standard smoothing invariant and its sufficient implications see [Lyubashevsky–Peikert–Regev, Definition 2.1 and Lemma 2.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) and [Peikert–Regev–Stephens-Davidowitz, Definition 2.4 and Lemma 2.5](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf). Root lattices as cyclotomic trace lattices are classical (see, e.g., [Galois trace forms of type A, D, E, §1](https://arxiv.org/abs/2307.06612)). Grouped phase-invariance and first circular moments are likewise classical (e.g. the von Mises discussion in [A Data Driven Smooth Test for Circular Uniformity](https://www.ism.ac.jp/editsec/aism/pdf/054_1_0029.pdf)); the calculation here is for the two exact prime-cyclotomic tori, with a separate high-dimensional dual-theta argument.

## Geometry, statements, and normalizations

Write H={x∈ℝ^p : Σ_i x_i=0}, let Π be its orthogonal projection, and set A=H∩ℤ^p. Its dual in H is A*=Πℤ^p: necessity follows from testing differences e_i−e_j and therefore checking that all coordinate differences are integers; sufficiency is immediate. The real Euclidean canonical embedding of ℤ[ζ_p] is isometric to √p A*. Indeed the trace inner products of the power basis have diagonal p−1 and off-diagonals −1, by the sum of nontrivial p-th roots. This is the Gram matrix of √p Πe_i for i=1,…,p−1, which form a basis of √p A*. The canonically embedded codifferent is its metric dual (conjugation preserves the codifferent), hence isometric to A/√p. We state all results at the unscaled A and A* units. Multiplying a lattice by a scalar multiplies every width appearing in the results by that scalar.

For a lattice Λ in H, write `D_s mod Λ` for a spherical Gaussian in H with density proportional to exp(−π‖x‖²/s²), then wrapped around H/Λ. Set r=e^(−πs²), and let I₀ be the modified Bessel function given by
```
I₀(x) = (1/2π)∫_(0)^(2π) exp(x cos θ)dθ = Σ_(j≥0) (x²/4)^j/(j!)² .
```
If p r²→τ∈[0,∞], the exact TV distances from Haar on these tori tend to
```
Λ=A:      2Φ(√(τ/2))−1 ,
Λ=A*:     E[(1−e^(−τ) I₀(2√τ |Z|))_+] ,
```
where Z is a centered complex Gaussian with independent real and imaginary parts N(0,1/2). Both limits are zero at τ=0 and one at τ=∞.

For comparison, at any fixed tolerance ε>0 their ordinary spherical smoothing parameters satisfy
```
π η_ε(A)²    = log p − log(c_A) + o(1),     c_A=(1/2)log(1+ε);
π η_ε(A*)²   = log p − log(c_A*)+ o(1),     I₀(2c_A*)=1+ε .
```
Thus the sufficient smoothing width is asymptotically √2 times the actual TV transition width in these coordinates. This does not contradict standard smoothing theorems, which give sufficient widths from an L¹ sum of nontrivial Fourier coefficients rather than claiming sharp TV.

## Theta limits, with control of high-support terms in the dual

For either lattice write Θ(Λ;t)=Σ_(x∈Λ)t^(‖x‖²), for 0<t<1. If p t→c∈[0,∞), then
```
Θ(A;t)→I₀(2c),       Θ(A*;t)→e^(2c).
```
The root theta series is the constant Fourier coefficient of `[Σ_(j∈ℤ) t^(j²) e^(ijθ)]^p`, which converges uniformly to exp(2c cos θ) because the scalar sum is 1+2t cos θ+O(t⁴). Integrating gives the claimed limit.

For A*, each point Πk has a unique integer representative k up to multiples of the all-ones vector, and we choose the representative with mean in [−1/2,1/2). Put b=|supp(k)| and E=‖Πk‖²=Σ k_i²−(Σ k_i)²/p. For b≤p^(1/3), Cauchy–Schwarz gives E≥(1−p^(−2/3))Σ k_i². Summing over **all** integer k with the latter exponent gives the upper bound `(Σ_j t^(j²(1−p^(−2/3))))^p→e^(2c)` for this sparse part when c>0. At any fixed support size b, the vectors with nonzero values only ±1 have E=b+O(b²/p), are centered representatives for p large, and contribute asymptotically (2c)^b/b!. The sum of these fixed-support contributions tends to the same limit as its support cutoff tends to infinity.

For completeness, the dense representatives contribute o(1). If p^(1/3)<b≤p/2, E≥(1−b/p)Σ k_i²; since t≤C/p and one-dimensional sums over nonzero coordinates with exponent γ∈[1/2,1] are O(t^γ), the total contribution at support size b is at most `(C' p^(b/p)/b)^b`, using the binomial coefficient bound. The base is uniformly O(p^(−1/12)) for b≤p/4, and O(p^(−1/2)) for b≥p/4 in this range. If b>p/2 the centered representative gives p·mean²≤(1/2)|Σ k_i|≤(1/2)Σ k_i², so E≥(1/2)Σ k_i² and the contribution is bounded by `(C' √p/b)^b`, again summable to o(1). If c=0 use monotonicity and let a positive upper bound c' on pt tend to zero. This proves the dual theta limit, and for finite positive c it also shows that bounded-support ±1 representatives capture asymptotically all mass as the support bound is increased.

Smoothing of Λ asks for Θ(Λ*;e^(−πs²))≤1+ε. The two theta limits have unique positive solutions in c and are strictly increasing, so comparison at constants just below and just above these solutions gives the stated smoothing widths.

## The dual torus: averaging the common phase

The torus H/A* is the quotient of the p-fold circle torus by its diagonal circle, via the linear projection Π. Consequently its Gaussian is the image of p independent one-dimensional wrapped Gaussians. The scalar Haar density is
```
g_r(x)=Σ_(j∈ℤ) r^(j²) exp(2πijx)
      =1+2r cos(2πx)+O(r⁴)
```
uniformly as r→0. With X_i independent Haar circle variables, the quotient density evaluated at their Haar image is
```
L(X)=∫_(0)^1 ∏_i g_r(X_i+θ) dθ .
```
Indeed integrating along the diagonal orbit is conditional expectation of the full density given the quotient. Suppose 0<τ<∞. Write S=Σ_i exp(2πi X_i). Expanding log g_r through order r², uniformly in θ, gives
```
log∏_i g_r(X_i+θ) = 2r Re(exp(2πiθ)S) − p r² + o_prob(1).
```
The summed cubic remainder is O(p r³)→0. The second Fourier harmonic term in the quadratic correction is O_prob(r²√p)→0 by its second moment; the deterministic part of Σ cos² is p/2. The two-dimensional central limit theorem gives S/√p⇒Z. Thus integration in θ yields the likelihood limit e^(−τ)I₀(2√τ|Z|). Uniformity of the log error makes the integrated numerator differ by a factor e^{o_prob(1)}; the Bessel integral itself is tight by the central limit theorem. TV is the expectation of the bounded continuous positive part (1−L)_+, giving the desired expression.

## The root torus: proving a product approximation on the hyperplane quotient

The torus H/A identifies with T₀={x∈(ℝ/ℤ)^p : Σ x_i=0 mod 1}. Its Haar law can be generated by p−1 independent Haar circle variables with the final coordinate the negative sum. The exact wrapped Gaussian coefficients on this subgroup, indexed by k modulo ℤ·1, are r^(‖Πk‖²). As an approximation use the Haar density
```
F(x)=∏_(i=1)^p g_r(x_i) / C_p ,      C_p=Σ_(m∈ℤ)r^(p m²).
```
Indeed integrating the product on T₀ retains exactly the equal-coordinate Fourier indices. More generally its coefficient at k is
```
(Σ_(m∈ℤ) r^(‖k+m·1‖²))/C_p
= r^(‖Πk‖²) [Σ_(m∈ℤ)r^(p(m+mean(k))²)]/C_p .
```
The factor in square brackets divided by C_p is bounded uniformly at the centered representative, via |mean(k)|≤1/2 and r→0. For k supported on a fixed number of ±1 coordinates it tends uniformly to one: the m=0 factor is r^(O(1/p))→1 and all others vanish. When 0<τ<∞ the preceding dual-theta result at t=r² says these bounded-support representatives capture asymptotically all squared coefficient mass as the bound grows. Parseval, the bounded factor on the rest, and choosing the cutoff large then p large show that F and the true Gaussian densities differ by o(1) in L², hence also in TV. In particular this does not simply identify conditioning on a wrapped sum with conditioning on a real sum; the estimate of their difference is necessary.

Since g_r=1+O(r) uniformly, C_p=1+O(r^p), and the first p−1 variables under Haar are independent, F also differs by o(1) in TV from the density ∏_(i<p) g_r(x_i). The log-likelihood of that product under Haar converges to N(−τ,2τ), by expanding as above without the average over θ and applying the one-dimensional central limit theorem. Evaluating the positive-part formula for TV gives the stated Gaussian expression.

For τ=0, the squared Fourier sum at t=r² tends to one for either dual lattice, so TV tends to zero by Cauchy–Schwarz. At τ=∞, in the real Gaussian before projecting, the independent wrapped coordinates' phase-vector sum has mean p r and variance at most p in squared complex norm. Its absolute value is invariant under subtracting their average, adding integer coordinates, and removing a common phase; it is therefore a legitimate statistic for both noise tori. Under Haar for either torus this absolute value is O_prob(√p), using the independent circle representation for A* and p−1 independent circles plus one bounded term for A. Chebyshev then separates these standalone noise distributions and Haar with probability tending to one. This is an endpoint argument on raw noise laws, not a test on any secret-bearing data.

## Comparison of the profiles

The natural map H/A→H/A* preserves Gaussian and Haar, so the dual profile cannot be larger. It is strictly smaller for finite τ>0: the root limiting likelihood equals e^(−τ+2√τ Re Z), and the dual limiting likelihood is its conditional expectation given |Z|. For positive probability of radii |Z|>√τ/2, the root likelihood varies above and below one with phase, so conditional convexity of (1−x)_+ is strict. For small τ the root profile is asymptotic to √(τ/π), whereas the dual profile is asymptotic to τ/e. For the latter expand I₀ at zero, use `0≤(1−e^(−τ)I₀(2√τ R))_+/τ≤1`, and note that R² is exponential of mean one, with E[(1−R²)_+]=1/e.

[The verifier](verify-prime-cyclotomic-wrapped-gaussian.js) checks the first theta coefficients by two independent exact finite constructions and illustrates the two limiting functions by deterministic quadrature. The asymptotics are proved above, not inferred from those illustrations.
