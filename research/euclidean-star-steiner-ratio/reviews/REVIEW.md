# Independent internal mathematical review: the star-Steiner ratio

**Verdict: PASS** for the frozen theorem at SHA-256 `d52187b44a97c7c1f773b42131aa133566233962e8e95dd784906ee765bf7788`. No gap found, including in the equality-of-slope case d=3. This is AI-assisted internal review, not formal verification or independent external peer review.

## 1. Definition, denominator and averaging

The star is rooted at an input point and the comparison star may be rooted anywhere in the same Euclidean space. For a set of at least two distinct points the unrestricted minimum W is positive. A minimizer exists: the objective is continuous, bounded below and tends to infinity as the root goes to infinity. If a minimizing root is a data point then S=W. If it is not, the weights proportional to 1/r_i are finite and positive. The discrete minimum S cannot exceed their average of the star costs. Expanding that average, symmetrizing i,j (the distance is symmetric) and squaring the resulting factor gives
    
    (1/r_i+1/r_j)²(r_i²+r_j²−2r_i r_j t)/4=(z+1)(z−t),
    z=(r_i/r_j+r_j/r_i)/2.

The two sides before taking square roots are nonnegative, and the diagonal correctly contributes zero. The double sum of z is the product of the sum of radii and the sum of reciprocals. Thus (1) is sufficient, without any putative independence between radius and direction. The proof is actually valid about any proposed reference root outside the data; no unspoken first-order condition on the median is used. Also c_d>1 since |e−U|≥1−e·U with strict inequality away from the two poles, and the latter projection has mean one.

## 2. The hyperbolic kernel, with an independent elementary proof

In the submitted route, the Euler product for cosh has positive zeros in imaginary coordinates π(j+1/2). Summing 2exp(−π(j+1/2)v) gives 1/sinh(πv/2), and the rescaling of the half-argument produces 1/sinh(πv). For y>0,
    
    (m−1/2)/sinh y − 1/sinh(2y) = [(2m−1)cosh y−1]/sinh(2y) ≥ 0.

The original logarithm integral is finite: near v=0 the 1−cos(sv) factor cancels the O(v⁻²) upper bound on the density; its tail is exponentially integrable. Truncation makes the cosine mass finite. Its cosine matrix is PSD since cos(s_i v−s_j v) is the Gram matrix of unit planar phases. Its entrywise exponential is PSD term by term, including the all-ones constant; the positive normalization and the entrywise limit preserve PSD. All factors and signs in (2) are correct.

**Short independent derivation (classical normalized Cauchy Gram).** For c>0 put A_i=exp(2c s_i). Then
    
    sech(c(s_i−s_j)) = 2√(A_i A_j)/(A_i+A_j)
       = ∫₀^∞ [√(2A_i) e^(−A_i v)][√(2A_j) e^(−A_j v)] dv.

Hence each such matrix is PSD. Since cosh s=2cosh²(s/2)−1,
    
    √(1+sech s) = (1−(1/2)sech²(s/2))^(−1/2).

The function (1−y/2)^(-1/2) has a convergent power series with nonnegative coefficients for |y|≤1. Apply it entrywise to the Schur square of the PSD sech(s/2) kernel. This proves B₁ is PSD; multiplying entrywise by the (m−1)st Schur power of the PSD sech(s) kernel proves (2) for all m. No infinite-divisibility result or Euler product is needed in this alternative proof. The elementary identity and Cauchy kernel method should not themselves be claimed as novel positive-definite-function theory.

## 3. Angular comparison, endpoints and signs

For z≥1, t∈[−1,1], the expansion parameter is t/z, and the coefficient of −a_m t^m in K is √(z(z+1))z^(−m)=B_m(s). For |y|<1 the Taylor coefficients of 1−√(1−y) are positive; hence their sum equals 1 by monotone convergence to y=1. The series therefore converges absolutely at y=±1 as well (the value there agrees by continuity). This includes pairs of equal radii, coincident directions, and opposite directions. For each finite set the finite pair sum and the series can be interchanged directly.

With the Euclidean tensor product inner product, arbitrary unit u has ⟨u^{⊗m},v_m⟩=E T^m, and ⟨v_m,v_m⟩ has exactly the same value by another integral. For odd m this value is zero; for even m it is nonnegative. Expanding the inner products of the centered tensors gives the matrix (t_ij^m−E T^m) with no missing multiplicity. Each Schur product with the PSD radial matrix has nonnegative quadratic form on the all-ones vector. Subtracting the angular terms in the series makes the observed sum **at most**, not at least, the rotationally averaged one. At no point is a pointwise angular bound needed.

## 4. Radial maximum and the three-dimensional boundary

At each t, the geometric mean of the two affine positive factors is concave on 0≤x≤1 and continuous at the boundary; averaging preserves this. Equivalently its second derivative where defined is −(1+t)²/[4((1+x)(1−xt))^{3/2}]. At the endpoint the left derivative of its expectation is the average of (1−3t)/(2√2√(1−t)). For x near 1 the derivatives are bounded in absolute value by a constant times 1+(1−t)^(-1/2); when d=3 the sphere-coordinate density is constant, and in d>3 it further vanishes at t=1. The integral weight (1−t)^(-1/2)(1−t²)^{(d−3)/2} gives y=(1−t)/2 a beta law with parameters ((d−2)/2,(d−1)/2). Thus the normalized weighted mean of t is exactly 1/(2d−3); the endpoint derivative is a positive constant times 1−3/(2d−3), zero for d=3 and positive in higher dimensions. For a concave F, F(x)≤F(1)+(x−1)F′(1−)≤F(1), including the equality-of-slope case. The endpoint equals E√(2−2T)=c_d, and K contributes the factor z as asserted.

**Independent d=3 check.** T is uniform, so for 0<x≤1 direct integration gives
    
    F₃(x)=[(1+x)²−(1−x)√(1−x²)]/(3x),
    4/3−F₃(x)=(1−x)[√(1−x²)−(1−x)]/(3x) ≥ 0.

Here 1−x²−(1−x)²=2x(1−x)≥0. This directly verifies the crucial bound and its orientation at the exceptional zero derivative.

## 5. Attaining the supremum in the limit; scope

A uniformly distributed sequence on the sphere may be chosen with distinct entries. Its normalized potential ∑|u−p_j|/N converges pointwise to the constant c_d by weak convergence; it converges uniformly using finite nets and the 1-Lipschitz norm bound. Consequently S(P_N)/N→c_d, and W(P_N)≤N by testing the origin. This gives the lower limit for the ratio; combined with the proved upper bound it establishes equality of the supremum without any assertion of attainment by a finite configuration. It yields 4/3 in d=3. The sphere construction and terminology are prior; see [Dumitrescu–Tóth–Xu](https://arxiv.org/abs/0806.4858) for the original three-dimensional conjecture and higher-dimensional sphere constants. No conclusion asserts the conjectural exact planar value 4/π or concerns general Steiner networks. As an attribution caution only, the planar bound 4/3 (weaker than the conjecture) was [publicly announced by W. Jung](https://abstracts.societyforscience.org/Home/PrintPdf/11362); no planarly novel result is certified here.

The independent standard-library checker compares exact rational expressions and encloses each radical to a rational interval. Its finite examples exercise both kinds of anisotropy (directions and radii), high tensor powers, and the borderline scalar sign. They are sanity checks, not the proof of its universal quantifiers.
